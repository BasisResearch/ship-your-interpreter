import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch02Part08
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part15
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part20
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part30
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch13Part25
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
import Vsa.Sim.OutputAliasTraceHalt
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD281_01 : TraceData :=
  { pc := 0x8000e400#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bc90#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 267,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD281_02 : TraceData :=
  { pc := 0x8000e408#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bc90#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 267,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD281_03 : TraceData :=
  { pc := 0x8000e418#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 267,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD281_04 : TraceData :=
  { pc := 0x8000e428#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 267,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg281_00 chain
  [(0x8000e3f0#64, 0x1656b33#32),
   (0x8000e3f4#64, 0xb0b1b#32),
   (0x8000e3f8#64, 0xb840413#32)]
    terminator ⟨0x8000e3fc#64, 0xfc941ce3#32, 0xe3#8, 0x1c#8, 0x94#8, 0xfc#8, .br bop.BNE false, 8, 9, 0x1fd8#13, 0#21, 0#12⟩

def traceLds281_00 : List (List (BitVec 8)) :=
  []

theorem facts281_00 : ChainFacts (writeLog snapshotMem traceD281.log)
    (writeLog snapshotMem traceD281.log) traceD281.regs traceLds281_00 traceSeg281_00 := by
  have kind0 : (mkLine 0x8000e3f0#64 0x1656b33#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x8000e3f4#64 0xb0b1b#32).kind = MKind.addiw := by decide
  have kind2 : (mkLine 0x8000e3f8#64 0xb840413#32).kind = MKind.addi := by decide
  simp only [traceSeg281_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_000b0b1b
    | exact DecodeTable.decode_01656b33
    | exact DecodeTable.decode_0b840413
    | exact DecodeTable.decode_fc941ce3
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run281_00 {c : Config} (h : TraceHolds traceD281 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD281_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg281_00 traceLds281_00 (by decide) facts281_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg281_00 (SegEvalState.init traceD281.regs traceLds281_00)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg281_00 (SegEvalState.init traceD281.regs traceLds281_00)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run281_00

#derive_case traceSeg281_01 chain
  [(0x8000e400#64, 0x93903#32)]
    terminator ⟨0x8000e404#64, 0xfa0912e3#32, 0xe3#8, 0x12#8, 0x09#8, 0xfa#8, .br bop.BNE false, 18, 0, 0x1fa4#13, 0#21, 0#12⟩

def traceLds281_01 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts281_01 : ChainFacts (writeLog snapshotMem traceD281_01.log)
    (writeLog snapshotMem traceD281_01.log) traceD281_01.regs traceLds281_01 traceSeg281_01 := by
  have kind0 : (mkLine 0x8000e400#64 0x93903#32).kind = MKind.ld := by decide
  simp only [traceSeg281_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00093903
    | exact DecodeTable.decode_fa0912e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run281_01 {c : Config} (h : TraceHolds traceD281_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD281_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg281_01 traceLds281_01 (by decide) facts281_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg281_01 (SegEvalState.init traceD281_01.regs traceLds281_01)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg281_01 (SegEvalState.init traceD281_01.regs traceLds281_01)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run281_01

#derive_case traceSeg281_02 chain
  [(0x8000e408#64, 0x4813083#32),
   (0x8000e40c#64, 0x4013403#32),
   (0x8000e410#64, 0x3813483#32),
   (0x8000e414#64, 0x3013903#32)]

def traceLds281_02 : List (List (BitVec 8)) :=
  [[0x88#8, 0x47#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts281_02 : ChainFacts (writeLog snapshotMem traceD281_02.log)
    (writeLog snapshotMem traceD281_02.log) traceD281_02.regs traceLds281_02 traceSeg281_02 := by
  have kind0 : (mkLine 0x8000e408#64 0x4813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e40c#64 0x4013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e410#64 0x3813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000e414#64 0x3013903#32).kind = MKind.ld := by decide
  simp only [traceSeg281_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_03013903
    | exact DecodeTable.decode_03813483
    | exact DecodeTable.decode_04013403
    | exact DecodeTable.decode_04813083
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run281_02 {c : Config} (h : TraceHolds traceD281_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD281_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg281_02 traceLds281_02 (by decide) facts281_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg281_02 (SegEvalState.init traceD281_02.regs traceLds281_02)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg281_02 (SegEvalState.init traceD281_02.regs traceLds281_02)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run281_02

#derive_case traceSeg281_03 chain
  [(0x8000e418#64, 0x2813983#32),
   (0x8000e41c#64, 0x2013a03#32),
   (0x8000e420#64, 0x1813a83#32),
   (0x8000e424#64, 0x813b83#32)]

def traceLds281_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts281_03 : ChainFacts (writeLog snapshotMem traceD281_03.log)
    (writeLog snapshotMem traceD281_03.log) traceD281_03.regs traceLds281_03 traceSeg281_03 := by
  have kind0 : (mkLine 0x8000e418#64 0x2813983#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e41c#64 0x2013a03#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e420#64 0x1813a83#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000e424#64 0x813b83#32).kind = MKind.ld := by decide
  simp only [traceSeg281_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00813b83
    | exact DecodeTable.decode_01813a83
    | exact DecodeTable.decode_02013a03
    | exact DecodeTable.decode_02813983
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run281_03 {c : Config} (h : TraceHolds traceD281_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD281_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg281_03 traceLds281_03 (by decide) facts281_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg281_03 (SegEvalState.init traceD281_03.regs traceLds281_03)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg281_03 (SegEvalState.init traceD281_03.regs traceLds281_03)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run281_03

#derive_case traceSeg281_04 chain
  [(0x8000e428#64, 0xb0513#32),
   (0x8000e42c#64, 0x1013b03#32),
   (0x8000e430#64, 0x5010113#32)]
    terminator ⟨0x8000e434#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds281_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts281_04 : ChainFacts (writeLog snapshotMem traceD281_04.log)
    (writeLog snapshotMem traceD281_04.log) traceD281_04.regs traceLds281_04 traceSeg281_04 := by
  have kind0 : (mkLine 0x8000e428#64 0xb0513#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e42c#64 0x1013b03#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e430#64 0x5010113#32).kind = MKind.addi := by decide
  simp only [traceSeg281_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_000b0513
    | exact DecodeTable.decode_01013b03
    | exact DecodeTable.decode_05010113
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run281_04 {c : Config} (h : TraceHolds traceD281_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD282 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg281_04 traceLds281_04 (by decide) facts281_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg281_04 (SegEvalState.init traceD281_04.regs traceLds281_04)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg281_04 (SegEvalState.init traceD281_04.regs traceLds281_04)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run281_04
theorem run281 {c : Config} (h : TraceHolds traceD281 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD282 c' := by
  obtain ⟨c0, s0, h0⟩ := run281_00 h
  obtain ⟨c1, s1, h1⟩ := run281_01 h0
  obtain ⟨c2, s2, h2⟩ := run281_02 h1
  obtain ⟨c3, s3, h3⟩ := run281_03 h2
  obtain ⟨c4, s4, h4⟩ := run281_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run281
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg282 chain
  [(0x80004788#64, 0x40513#32)]

def traceLds282 : List (List (BitVec 8)) :=
  []

theorem facts282 : ChainFacts (writeLog snapshotMem traceD282.log)
    (writeLog snapshotMem traceD282.log) traceD282.regs traceLds282 traceSeg282 := by
  have kind0 : (mkLine 0x80004788#64 0x40513#32).kind = MKind.addi := by decide
  simp only [traceSeg282, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00040513
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run282 {c : Config} (h : TraceHolds traceD282 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD283 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg282 traceLds282 (by decide) facts282 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg282 (SegEvalState.init traceD282.regs traceLds282)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg282 (SegEvalState.init traceD282.regs traceLds282)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run282
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts283 : TraceCallFacts traceD283 0x9f5fb0ef#32
    (instruction.JAL (0x1fb9f4#21, gprIdx 1)) 0xef#8 0xb0#8 0x5f#8 0x9f#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_9f5fb0ef

theorem run283 {c : Config} (h : TraceHolds traceD283 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD284 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x9f5fb0ef#32 0x1fb9f4#21 0xef#8 0xb0#8 0x5f#8 0x9f#8 facts283 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run283
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg284 chain
  [(0x80000180#64, 0x2051713#32),
   (0x80000184#64, 0x1f75793#32),
   (0x80000188#64, 0x17e793#32),
   (0x8000018c#64, 0x1b717#32)]

def traceLds284 : List (List (BitVec 8)) :=
  []

theorem facts284 : ChainFacts (writeLog snapshotMem traceD284.log)
    (writeLog snapshotMem traceD284.log) traceD284.regs traceLds284 traceSeg284 := by
  have kind0 : (mkLine 0x80000180#64 0x2051713#32).kind = MKind.slli := by decide
  have kind1 : (mkLine 0x80000184#64 0x1f75793#32).kind = MKind.srli := by decide
  have kind2 : (mkLine 0x80000188#64 0x17e793#32).kind = MKind.ori := by decide
  have kind3 : (mkLine 0x8000018c#64 0x1b717#32).kind = MKind.auipc := by decide
  simp only [traceSeg284, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0001b717
    | exact DecodeTable.decode_0017e793
    | exact DecodeTable.decode_01f75793
    | exact DecodeTable.decode_02051713
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run284 {c : Config} (h : TraceHolds traceD284 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD285 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg284 traceLds284 (by decide) facts284 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 267 ++ (evalBlocks traceSeg284 (SegEvalState.init traceD284.regs traceLds284)).log = traceStores.take 267
  have hw : (evalBlocks traceSeg284 (SegEvalState.init traceD284.regs traceLds284)).log = (traceStores.drop 267).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run284
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem run285 {c : Config} (h : TraceHolds traceD285 c) :
    ∃ σf, Halted c 0 σf ∧ σf.sailOutput = #["\n", "\n"] := by
  exact h.halted0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

#print axioms run285
end Vsa.Sim.OutputAliasLoaded
