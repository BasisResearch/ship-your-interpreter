import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part03
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part30
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part04
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part25
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch13Part09
import Vsa.Sim.DecodeTable.Batch14Part26
import Vsa.Sim.DecodeTable.Batch15Part09
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts261 : TraceCallFacts traceD261 0x12c000ef#32
    (instruction.JAL (0x12c#21, gprIdx 1)) 0xef#8 0x0#8 0xc0#8 0x12#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_12c000ef

theorem run261 {c : Config} (h : TraceHolds traceD261 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x12c000ef#32 0x12c#21 0xef#8 0x0#8 0xc0#8 0x12#8 facts261 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run261
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD262_01 : TraceData :=
  { pc := 0x8000eb80#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x12#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 261,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_02 : TraceData :=
  { pc := 0x8000eb94#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 262,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_03 : TraceData :=
  { pc := 0x8000eba4#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x812#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 262,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_04 : TraceData :=
  { pc := 0x8000ed40#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x812#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 263,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_05 : TraceData :=
  { pc := 0x8000ed48#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x812#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 263,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_06 : TraceData :=
  { pc := 0x8000ec9c#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x812#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 263,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD262_07 : TraceData :=
  { pc := 0x8000ecac#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x0#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x812#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 263,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg262_00 chain
  [(0x8000eb70#64, 0x1059703#32),
   (0x8000eb74#64, 0xfd010113#32),
   (0x8000eb78#64, 0x2813023#32),
   (0x8000eb7c#64, 0x1313423#32)]

def traceLds262_00 : List (List (BitVec 8)) :=
  [[0x12#8, 0x0#8]]

theorem facts262_00 : ChainFacts (writeLog snapshotMem traceD262.log)
    (writeLog snapshotMem traceD262.log) traceD262.regs traceLds262_00 traceSeg262_00 := by
  have kind0 : (mkLine 0x8000eb70#64 0x1059703#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000eb74#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb78#64 0x2813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000eb7c#64 0x1313423#32).kind = MKind.sd := by decide
  simp only [traceSeg262_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01059703
    | exact DecodeTable.decode_01313423
    | exact DecodeTable.decode_02813023
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_00 {c : Config} (h : TraceHolds traceD262 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_00 traceLds262_00 (by decide) facts262_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg262_00 (SegEvalState.init traceD262.regs traceLds262_00)).log = traceStores.take 261
  have hw : (evalBlocks traceSeg262_00 (SegEvalState.init traceD262.regs traceLds262_00)).log = (traceStores.drop 259).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_00

#derive_case traceSeg262_01 chain
  [(0x8000eb80#64, 0x2113423#32),
   (0x8000eb84#64, 0x877793#32),
   (0x8000eb88#64, 0x58413#32),
   (0x8000eb8c#64, 0x50993#32)]
    terminator ⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE false, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds262_01 : List (List (BitVec 8)) :=
  []

theorem facts262_01 : ChainFacts (writeLog snapshotMem traceD262_01.log)
    (writeLog snapshotMem traceD262_01.log) traceD262_01.regs traceLds262_01 traceSeg262_01 := by
  have kind0 : (mkLine 0x8000eb80#64 0x2113423#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000eb84#64 0x877793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000eb88#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000eb8c#64 0x50993#32).kind = MKind.addi := by decide
  simp only [traceSeg262_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050993
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00877793
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_12079263
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_01 {c : Config} (h : TraceHolds traceD262_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_01 traceLds262_01 (by decide) facts262_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 261 ++ (evalBlocks traceSeg262_01 (SegEvalState.init traceD262_01.regs traceLds262_01)).log = traceStores.take 262
  have hw : (evalBlocks traceSeg262_01 (SegEvalState.init traceD262_01.regs traceLds262_01)).log = (traceStores.drop 261).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_01

#derive_case traceSeg262_02 chain
  [(0x8000eb94#64, 0x17b7#32),
   (0x8000eb98#64, 0x80078793#32),
   (0x8000eb9c#64, 0x85a683#32),
   (0x8000eba0#64, 0xf767b3#32)]

def traceLds262_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts262_02 : ChainFacts (writeLog snapshotMem traceD262_02.log)
    (writeLog snapshotMem traceD262_02.log) traceD262_02.regs traceLds262_02 traceSeg262_02 := by
  have kind0 : (mkLine 0x8000eb94#64 0x17b7#32).kind = MKind.lui := by decide
  have kind1 : (mkLine 0x8000eb98#64 0x80078793#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb9c#64 0x85a683#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000eba0#64 0xf767b3#32).kind = MKind.or := by decide
  simp only [traceSeg262_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_000017b7
    | exact DecodeTable.decode_0085a683
    | exact DecodeTable.decode_00f767b3
    | exact DecodeTable.decode_80078793
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_02 {c : Config} (h : TraceHolds traceD262_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_02 traceLds262_02 (by decide) facts262_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 262 ++ (evalBlocks traceSeg262_02 (SegEvalState.init traceD262_02.regs traceLds262_02)).log = traceStores.take 262
  have hw : (evalBlocks traceSeg262_02 (SegEvalState.init traceD262_02.regs traceLds262_02)).log = (traceStores.drop 262).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_02

#derive_case traceSeg262_03 chain
  [(0x8000eba4#64, 0xf59823#32)]
    terminator ⟨0x8000eba8#64, 0x18d05c63#32, 0x63#8, 0x5c#8, 0xd0#8, 0x18#8, .br bop.BGE true, 0, 13, 0x0198#13, 0#21, 0#12⟩

def traceLds262_03 : List (List (BitVec 8)) :=
  []

theorem facts262_03 : ChainFacts (writeLog snapshotMem traceD262_03.log)
    (writeLog snapshotMem traceD262_03.log) traceD262_03.regs traceLds262_03 traceSeg262_03 := by
  have kind0 : (mkLine 0x8000eba4#64 0xf59823#32).kind = MKind.sh := by decide
  simp only [traceSeg262_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00f59823
    | exact DecodeTable.decode_18d05c63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_03 {c : Config} (h : TraceHolds traceD262_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_03 traceLds262_03 (by decide) facts262_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 262 ++ (evalBlocks traceSeg262_03 (SegEvalState.init traceD262_03.regs traceLds262_03)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg262_03 (SegEvalState.init traceD262_03.regs traceLds262_03)).log = (traceStores.drop 262).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_03

#derive_case traceSeg262_04 chain
  [(0x8000ed40#64, 0x705a683#32)]
    terminator ⟨0x8000ed44#64, 0xe6d044e3#32, 0xe3#8, 0x44#8, 0xd0#8, 0xe6#8, .br bop.BLT false, 0, 13, 0x1e68#13, 0#21, 0#12⟩

def traceLds262_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts262_04 : ChainFacts (writeLog snapshotMem traceD262_04.log)
    (writeLog snapshotMem traceD262_04.log) traceD262_04.regs traceLds262_04 traceSeg262_04 := by
  have kind0 : (mkLine 0x8000ed40#64 0x705a683#32).kind = MKind.lw := by decide
  simp only [traceSeg262_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0705a683
    | exact DecodeTable.decode_e6d044e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_04 {c : Config} (h : TraceHolds traceD262_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_04 traceLds262_04 (by decide) facts262_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg262_04 (SegEvalState.init traceD262_04.regs traceLds262_04)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg262_04 (SegEvalState.init traceD262_04.regs traceLds262_04)).log = (traceStores.drop 263).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_04

#derive_case traceSeg262_05 chain
  []
    terminator ⟨0x8000ed48#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0#13, 0x1fff54#21, 0#12⟩

def traceLds262_05 : List (List (BitVec 8)) :=
  []

theorem facts262_05 : ChainFacts (writeLog snapshotMem traceD262_05.log)
    (writeLog snapshotMem traceD262_05.log) traceD262_05.regs traceLds262_05 traceSeg262_05 := by
  simp only [traceSeg262_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_f55ff06f
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_05 {c : Config} (h : TraceHolds traceD262_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_05 traceLds262_05 (by decide) facts262_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg262_05 (SegEvalState.init traceD262_05.regs traceLds262_05)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg262_05 (SegEvalState.init traceD262_05.regs traceLds262_05)).log = (traceStores.drop 263).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_05

#derive_case traceSeg262_06 chain
  [(0x8000ec9c#64, 0x2813083#32),
   (0x8000eca0#64, 0x2013403#32),
   (0x8000eca4#64, 0x813983#32),
   (0x8000eca8#64, 0x513#32)]

def traceLds262_06 : List (List (BitVec 8)) :=
  [[0x48#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8]]

theorem facts262_06 : ChainFacts (writeLog snapshotMem traceD262_06.log)
    (writeLog snapshotMem traceD262_06.log) traceD262_06.regs traceLds262_06 traceSeg262_06 := by
  have kind0 : (mkLine 0x8000ec9c#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eca0#64 0x2013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eca4#64 0x813983#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eca8#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg262_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00813983
    | exact DecodeTable.decode_02013403
    | exact DecodeTable.decode_02813083
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_06 {c : Config} (h : TraceHolds traceD262_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD262_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_06 traceLds262_06 (by decide) facts262_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg262_06 (SegEvalState.init traceD262_06.regs traceLds262_06)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg262_06 (SegEvalState.init traceD262_06.regs traceLds262_06)).log = (traceStores.drop 263).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_06

#derive_case traceSeg262_07 chain
  [(0x8000ecac#64, 0x3010113#32)]
    terminator ⟨0x8000ecb0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds262_07 : List (List (BitVec 8)) :=
  []

theorem facts262_07 : ChainFacts (writeLog snapshotMem traceD262_07.log)
    (writeLog snapshotMem traceD262_07.log) traceD262_07.regs traceLds262_07 traceSeg262_07 := by
  have kind0 : (mkLine 0x8000ecac#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg262_07, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_03010113
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run262_07 {c : Config} (h : TraceHolds traceD262_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD263 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg262_07 traceLds262_07 (by decide) facts262_07 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg262_07 (SegEvalState.init traceD262_07.regs traceLds262_07)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg262_07 (SegEvalState.init traceD262_07.regs traceLds262_07)).log = (traceStores.drop 263).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run262_07
theorem run262 {c : Config} (h : TraceHolds traceD262 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD263 c' := by
  obtain ⟨c0, s0, h0⟩ := run262_00 h
  obtain ⟨c1, s1, h1⟩ := run262_01 h0
  obtain ⟨c2, s2, h2⟩ := run262_02 h1
  obtain ⟨c3, s3, h3⟩ := run262_03 h2
  obtain ⟨c4, s4, h4⟩ := run262_04 h3
  obtain ⟨c5, s5, h5⟩ := run262_05 h4
  obtain ⟨c6, s6, h6⟩ := run262_06 h5
  obtain ⟨c7, s7, h7⟩ := run262_07 h6
  exact ⟨c7, (((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7, h7⟩

#print axioms run262
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg263 chain
  [(0x8000ea48#64, 0x5043783#32),
   (0x8000ea4c#64, 0x50913#32)]
    terminator ⟨0x8000ea50#64, 0x00078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8000ea54#64, 0x3043583#32),
   (0x8000ea58#64, 0x48513#32)]

def traceLds263 : List (List (BitVec 8)) :=
  [[0xc0#8, 0xf0#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts263 : ChainFacts (writeLog snapshotMem traceD263.log)
    (writeLog snapshotMem traceD263.log) traceD263.regs traceLds263 traceSeg263 := by
  have kind0 : (mkLine 0x8000ea48#64 0x5043783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ea4c#64 0x50913#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea54#64 0x3043583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea58#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg263, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00050913
    | exact DecodeTable.decode_00078a63
    | exact DecodeTable.decode_03043583
    | exact OutputAliasDecode.decode_05043783
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run263 {c : Config} (h : TraceHolds traceD263 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD264 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg263 traceLds263 (by decide) facts263 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg263 (SegEvalState.init traceD263.regs traceLds263)).log = traceStores.take 263
  have hw : (evalBlocks traceSeg263 (SegEvalState.init traceD263.regs traceLds263)).log = (traceStores.drop 263).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run263
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts264 : TraceCallFacts traceD264 0x780e7#32
    (instruction.JALR (0x0#12, gprIdx 15, gprIdx 1)) 0xe7#8 0x80#8 0x7#8 0x0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_000780e7

theorem run264 {c : Config} (h : TraceHolds traceD264 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD265 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x8000f0c0#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts264
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run264
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg265 chain
  [(0x8000f0c0#64, 0x1259583#32)]
    terminator ⟨0x8000f0c4#64, 0x1a40106f#32, 0x6f#8, 0x10#8, 0x40#8, 0x1a#8, .j, 0, 0, 0#13, 0x0011a4#21, 0#12⟩ ;;
  [(0x80010268#64, 0xff010113#32),
   (0x8001026c#64, 0x813023#32),
   (0x80010270#64, 0x50413#32),
   (0x80010274#64, 0x58513#32),
   (0x80010278#64, 0x4e01ac23#32),
   (0x8001027c#64, 0x113423#32)]

def traceLds265 : List (List (BitVec 8)) :=
  [[0x2#8, 0x0#8]]

theorem facts265 : ChainFacts (writeLog snapshotMem traceD265.log)
    (writeLog snapshotMem traceD265.log) traceD265.regs traceLds265 traceSeg265 := by
  have kind0 : (mkLine 0x8000f0c0#64 0x1259583#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x80010268#64 0xff010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8001026c#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80010270#64 0x50413#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80010274#64 0x58513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80010278#64 0x4e01ac23#32).kind = MKind.sw := by decide
  have kind6 : (mkLine 0x8001027c#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg265, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050413
    | exact DecodeTable.decode_00058513
    | exact DecodeTable.decode_00113423
    | exact DecodeTable.decode_00813023
    | exact DecodeTable.decode_01259583
    | exact DecodeTable.decode_4e01ac23
    | exact DecodeTable.decode_ff010113
    | exact OutputAliasDecode.decode_1a40106f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run265 {c : Config} (h : TraceHolds traceD265 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD266 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg265 traceLds265 (by decide) facts265 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 263 ++ (evalBlocks traceSeg265 (SegEvalState.init traceD265.regs traceLds265)).log = traceStores.take 266
  have hw : (evalBlocks traceSeg265 (SegEvalState.init traceD265.regs traceLds265)).log = (traceStores.drop 263).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run265
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts266 : TraceCallFacts traceD266 0xe19ef0ef#32
    (instruction.JAL (0x1efe18#21, gprIdx 1)) 0xef#8 0xf0#8 0x9e#8 0xe1#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_e19ef0ef

theorem run266 {c : Config} (h : TraceHolds traceD266 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD267 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe19ef0ef#32 0x1efe18#21 0xef#8 0xf0#8 0x9e#8 0xe1#8 facts266 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run266
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg267 chain
  [(0x80000098#64, 0x513#32)]
    terminator ⟨0x8000009c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds267 : List (List (BitVec 8)) :=
  []

theorem facts267 : ChainFacts (writeLog snapshotMem traceD267.log)
    (writeLog snapshotMem traceD267.log) traceD267.regs traceLds267 traceSeg267 := by
  have kind0 : (mkLine 0x80000098#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg267, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run267 {c : Config} (h : TraceHolds traceD267 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD268 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg267 traceLds267 (by decide) facts267 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 266 ++ (evalBlocks traceSeg267 (SegEvalState.init traceD267.regs traceLds267)).log = traceStores.take 266
  have hw : (evalBlocks traceSeg267 (SegEvalState.init traceD267.regs traceLds267)).log = (traceStores.drop 266).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run267
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg268 chain
  [(0x80010284#64, 0xfff00793#32)]
    terminator ⟨0x80010288#64, 0x00f50a63#32, 0x63#8, 0x0a#8, 0xf5#8, 0x00#8, .br bop.BEQ false, 10, 15, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8001028c#64, 0x813083#32),
   (0x80010290#64, 0x13403#32),
   (0x80010294#64, 0x1010113#32)]
    terminator ⟨0x80010298#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds268 : List (List (BitVec 8)) :=
  [[0x60#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts268 : ChainFacts (writeLog snapshotMem traceD268.log)
    (writeLog snapshotMem traceD268.log) traceD268.regs traceLds268 traceSeg268 := by
  have kind0 : (mkLine 0x80010284#64 0xfff00793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8001028c#64 0x813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80010290#64 0x13403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80010294#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg268, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00013403
    | exact DecodeTable.decode_00813083
    | exact DecodeTable.decode_00f50a63
    | exact DecodeTable.decode_01010113
    | exact DecodeTable.decode_fff00793
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run268 {c : Config} (h : TraceHolds traceD268 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD269 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg268 traceLds268 (by decide) facts268 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 266 ++ (evalBlocks traceSeg268 (SegEvalState.init traceD268.regs traceLds268)).log = traceStores.take 266
  have hw : (evalBlocks traceSeg268 (SegEvalState.init traceD268.regs traceLds268)).log = (traceStores.drop 266).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run268
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg269 chain
  []
    terminator ⟨0x8000ea60#64, 0x0a054063#32, 0x63#8, 0x40#8, 0x05#8, 0x0a#8, .br bop.BLT false, 10, 0, 0x00a0#13, 0#21, 0#12⟩ ;;
  [(0x8000ea64#64, 0x1045783#32),
   (0x8000ea68#64, 0x807f793#32)]
    terminator ⟨0x8000ea6c#64, 0x0a079263#32, 0x63#8, 0x92#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00a4#13, 0#21, 0#12⟩ ;;
  [(0x8000ea70#64, 0x5843583#32)]
    terminator ⟨0x8000ea74#64, 0x00058c63#32, 0x63#8, 0x8c#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x8000ea8c#64, 0x7843583#32)]
    terminator ⟨0x8000ea90#64, 0x00058863#32, 0x63#8, 0x88#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0010#13, 0#21, 0#12⟩

def traceLds269 : List (List (BitVec 8)) :=
  [[0x12#8, 0x8#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts269 : ChainFacts (writeLog snapshotMem traceD269.log)
    (writeLog snapshotMem traceD269.log) traceD269.regs traceLds269 traceSeg269 := by
  have kind0 : (mkLine 0x8000ea64#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind1 : (mkLine 0x8000ea68#64 0x807f793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000ea70#64 0x5843583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea8c#64 0x7843583#32).kind = MKind.ld := by decide
  simp only [traceSeg269, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_05843583
    | exact DecodeTable.decode_0807f793
    | exact DecodeTable.decode_0a079263
    | exact OutputAliasDecode.decode_00058863
    | exact OutputAliasDecode.decode_00058c63
    | exact OutputAliasDecode.decode_07843583
    | exact OutputAliasDecode.decode_0a054063
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run269 {c : Config} (h : TraceHolds traceD269 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD270 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg269 traceLds269 (by decide) facts269 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 266 ++ (evalBlocks traceSeg269 (SegEvalState.init traceD269.regs traceLds269)).log = traceStores.take 266
  have hw : (evalBlocks traceSeg269 (SegEvalState.init traceD269.regs traceLds269)).log = (traceStores.drop 266).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run269
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts270 : TraceCallFacts traceD270 0xe80f70ef#32
    (instruction.JAL (0x1f7680#21, gprIdx 1)) 0xef#8 0x70#8 0xf#8 0xe8#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_e80f70ef

theorem run270 {c : Config} (h : TraceHolds traceD270 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD271 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe80f70ef#32 0x1f7680#21 0xef#8 0x70#8 0xf#8 0xe8#8 facts270 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run270
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg271 chain
  [(0x80006120#64, 0x4e018513#32)]
    terminator ⟨0x80006124#64, 0x6bd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6b#8, .j, 0, 0, 0#13, 0x000ebc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds271 : List (List (BitVec 8)) :=
  []

theorem facts271 : ChainFacts (writeLog snapshotMem traceD271.log)
    (writeLog snapshotMem traceD271.log) traceD271.regs traceLds271 traceSeg271 := by
  have kind0 : (mkLine 0x80006120#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg271, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6bd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run271 {c : Config} (h : TraceHolds traceD271 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD272 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg271 traceLds271 (by decide) facts271 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 266 ++ (evalBlocks traceSeg271 (SegEvalState.init traceD271.regs traceLds271)).log = traceStores.take 266
  have hw : (evalBlocks traceSeg271 (SegEvalState.init traceD271.regs traceLds271)).log = (traceStores.drop 266).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run271
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg272 chain
  [(0x8000eaa4#64, 0xb042783#32),
   (0x8000eaa8#64, 0x41823#32),
   (0x8000eaac#64, 0x17f793#32)]
    terminator ⟨0x8000eab0#64, 0x0a078463#32, 0x63#8, 0x84#8, 0x07#8, 0x0a#8, .br bop.BEQ true, 15, 0, 0x00a8#13, 0#21, 0#12⟩ ;;
  [(0x8000eb58#64, 0xa043503#32)]

def traceLds272 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts272 : ChainFacts (writeLog snapshotMem traceD272.log)
    (writeLog snapshotMem traceD272.log) traceD272.regs traceLds272 traceSeg272 := by
  have kind0 : (mkLine 0x8000eaa4#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000eaa8#64 0x41823#32).kind = MKind.sh := by decide
  have kind2 : (mkLine 0x8000eaac#64 0x17f793#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eb58#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg272, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_0a043503
    | exact DecodeTable.decode_0b042783
    | exact OutputAliasDecode.decode_00041823
    | exact OutputAliasDecode.decode_0a078463
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run272 {c : Config} (h : TraceHolds traceD272 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD273 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg272 traceLds272 (by decide) facts272 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 266 ++ (evalBlocks traceSeg272 (SegEvalState.init traceD272.regs traceLds272)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg272 (SegEvalState.init traceD272.regs traceLds272)).log = (traceStores.drop 266).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run272
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts273 : TraceCallFacts traceD273 0xc9cf80ef#32
    (instruction.JAL (0x1f849c#21, gprIdx 1)) 0xef#8 0x80#8 0xcf#8 0xc9#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_c9cf80ef

theorem run273 {c : Config} (h : TraceHolds traceD273 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD274 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc9cf80ef#32 0x1f849c#21 0xef#8 0x80#8 0xcf#8 0xc9#8 facts273 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run273
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg274 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds274 : List (List (BitVec 8)) :=
  []

theorem facts274 : ChainFacts (writeLog snapshotMem traceD274.log)
    (writeLog snapshotMem traceD274.log) traceD274.regs traceLds274 traceSeg274 := by
  simp only [traceSeg274, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run274 {c : Config} (h : TraceHolds traceD274 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD275 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg274 traceLds274 (by decide) facts274 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg274 (SegEvalState.init traceD274.regs traceLds274)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg274 (SegEvalState.init traceD274.regs traceLds274)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run274
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg275 chain
  []
    terminator ⟨0x8000eb60#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0#13, 0x1fff54#21, 0#12⟩ ;;
  [(0x8000eab4#64, 0xa043503#32)]

def traceLds275 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts275 : ChainFacts (writeLog snapshotMem traceD275.log)
    (writeLog snapshotMem traceD275.log) traceD275.regs traceLds275 traceSeg275 := by
  have kind0 : (mkLine 0x8000eab4#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg275, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | exact DecodeTable.decode_f55ff06f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run275 {c : Config} (h : TraceHolds traceD275 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD276 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg275 traceLds275 (by decide) facts275 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg275 (SegEvalState.init traceD275.regs traceLds275)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg275 (SegEvalState.init traceD275.regs traceLds275)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run275
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts276 : TraceCallFacts traceD276 0xd20f80ef#32
    (instruction.JAL (0x1f8520#21, gprIdx 1)) 0xef#8 0x80#8 0xf#8 0xd2#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_d20f80ef

theorem run276 {c : Config} (h : TraceHolds traceD276 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD277 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xd20f80ef#32 0x1f8520#21 0xef#8 0x80#8 0xf#8 0xd2#8 facts276 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run276
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg277 chain
  []
    terminator ⟨0x80006fd8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds277 : List (List (BitVec 8)) :=
  []

theorem facts277 : ChainFacts (writeLog snapshotMem traceD277.log)
    (writeLog snapshotMem traceD277.log) traceD277.regs traceLds277 traceSeg277 := by
  simp only [traceSeg277, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run277 {c : Config} (h : TraceHolds traceD277 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD278 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg277 traceLds277 (by decide) facts277 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg277 (SegEvalState.init traceD277.regs traceLds277)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg277 (SegEvalState.init traceD277.regs traceLds277)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run277
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts278 : TraceCallFacts traceD278 0xe6cf70ef#32
    (instruction.JAL (0x1f766c#21, gprIdx 1)) 0xef#8 0x70#8 0xcf#8 0xe6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_e6cf70ef

theorem run278 {c : Config} (h : TraceHolds traceD278 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD279 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe6cf70ef#32 0x1f766c#21 0xef#8 0x70#8 0xcf#8 0xe6#8 facts278 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run278
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg279 chain
  [(0x80006128#64, 0x4e018513#32)]
    terminator ⟨0x8000612c#64, 0x6cd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6c#8, .j, 0, 0, 0#13, 0x000ecc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds279 : List (List (BitVec 8)) :=
  []

theorem facts279 : ChainFacts (writeLog snapshotMem traceD279.log)
    (writeLog snapshotMem traceD279.log) traceD279.regs traceLds279 traceSeg279 := by
  have kind0 : (mkLine 0x80006128#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg279, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6cd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run279 {c : Config} (h : TraceHolds traceD279 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD280 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg279 traceLds279 (by decide) facts279 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg279 (SegEvalState.init traceD279.regs traceLds279)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg279 (SegEvalState.init traceD279.regs traceLds279)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run279
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg280 chain
  [(0x8000eac0#64, 0x1813083#32),
   (0x8000eac4#64, 0x1013403#32),
   (0x8000eac8#64, 0x813483#32),
   (0x8000eacc#64, 0x90513#32),
   (0x8000ead0#64, 0x13903#32),
   (0x8000ead4#64, 0x2010113#32)]
    terminator ⟨0x8000ead8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds280 : List (List (BitVec 8)) :=
  [[0xf0#8, 0xe3#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x90#8, 0xbc#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts280 : ChainFacts (writeLog snapshotMem traceD280.log)
    (writeLog snapshotMem traceD280.log) traceD280.regs traceLds280 traceSeg280 := by
  have kind0 : (mkLine 0x8000eac0#64 0x1813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eac4#64 0x1013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eac8#64 0x813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eacc#64 0x90513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000ead0#64 0x13903#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000ead4#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg280, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00090513
    | exact DecodeTable.decode_01013403
    | exact DecodeTable.decode_01813083
    | exact DecodeTable.decode_02010113
    | exact OutputAliasDecode.decode_00013903
    | exact OutputAliasDecode.decode_00813483
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run280 {c : Config} (h : TraceHolds traceD280 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD281 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg280 traceLds280 (by decide) facts280 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg280 (SegEvalState.init traceD280.regs traceLds280)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg280 (SegEvalState.init traceD280.regs traceLds280)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run280
end Vsa.Sim.OutputAliasLoaded
