import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part02
import Vsa.Sim.DecodeTable.Batch01Part03
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part30
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch04Part32
import Vsa.Sim.DecodeTable.Batch05Part04
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part13
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part25
import Vsa.Sim.DecodeTable.Batch05Part29
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch05Part32
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part26
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part32
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part29
import Vsa.Sim.DecodeTable.Batch07Part30
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch12Part09
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch13Part09
import Vsa.Sim.DecodeTable.Batch15Part09
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg201 chain
  [(0x8000477c#64, 0x4a01b783#32)]
    terminator ⟨0x80004780#64, 0x00078463#32, 0x63#8, 0x84#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x0008#13, 0#21, 0#12⟩

def traceLds201 : List (List (BitVec 8)) :=
  [[0x18#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts201 : ChainFacts (writeLog snapshotMem traceD201.log)
    (writeLog snapshotMem traceD201.log) traceD201.regs traceLds201 traceSeg201 := by
  have kind0 : (mkLine 0x8000477c#64 0x4a01b783#32).kind = MKind.ld := by decide
  simp only [traceSeg201, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00078463
    | exact DecodeTable.decode_4a01b783
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run201 {c : Config} (h : TraceHolds traceD201 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD202 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg201 traceLds201 (by decide) facts201 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 219 ++ (evalBlocks traceSeg201 (SegEvalState.init traceD201.regs traceLds201)).log = traceStores.take 219
  have hw : (evalBlocks traceSeg201 (SegEvalState.init traceD201.regs traceLds201)).log = (traceStores.drop 219).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run201
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts202 : TraceCallFacts traceD202 0x780e7#32
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

theorem run202 {c : Config} (h : TraceHolds traceD202 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x80005d18#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts202
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run202
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD203_01 : TraceData :=
  { pc := 0x8000e368#64,
    regs := [(1, 0x80004788#64), (2, 0x87fffff0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x80005d18#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 219,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD203_02 : TraceData :=
  { pc := 0x8000e388#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x80005d18#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 226,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD203_03 : TraceData :=
  { pc := 0x8000e3a8#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x80005d18#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 228,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD203_04 : TraceData :=
  { pc := 0x8000e3b0#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x3#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 228,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD203_05 : TraceData :=
  { pc := 0x8000e3d0#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x228#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x3#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 228,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD203_06 : TraceData :=
  { pc := 0x8000e3dc#64,
    regs := [(1, 0x80004788#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001bc90#64), (10, 0x8001b538#64), (11, 0x8000e9f8#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x4#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 228,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg203_00 chain
  [(0x80005d18#64, 0x1018613#32),
   (0x80005d1c#64, 0x9597#32),
   (0x80005d20#64, 0xcdc58593#32),
   (0x80005d24#64, 0x2818513#32)]
    terminator ⟨0x80005d28#64, 0x6400806f#32, 0x6f#8, 0x80#8, 0x00#8, 0x64#8, .j, 0, 0, 0#13, 0x008640#21, 0#12⟩

def traceLds203_00 : List (List (BitVec 8)) :=
  []

theorem facts203_00 : ChainFacts (writeLog snapshotMem traceD203.log)
    (writeLog snapshotMem traceD203.log) traceD203.regs traceLds203_00 traceSeg203_00 := by
  have kind0 : (mkLine 0x80005d18#64 0x1018613#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80005d1c#64 0x9597#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80005d20#64 0xcdc58593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80005d24#64 0x2818513#32).kind = MKind.addi := by decide
  simp only [traceSeg203_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00009597
    | exact DecodeTable.decode_01018613
    | exact DecodeTable.decode_02818513
    | exact DecodeTable.decode_6400806f
    | exact DecodeTable.decode_cdc58593
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_00 {c : Config} (h : TraceHolds traceD203 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_00 traceLds203_00 (by decide) facts203_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 219 ++ (evalBlocks traceSeg203_00 (SegEvalState.init traceD203.regs traceLds203_00)).log = traceStores.take 219
  have hw : (evalBlocks traceSeg203_00 (SegEvalState.init traceD203.regs traceLds203_00)).log = (traceStores.drop 219).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_00

#derive_case traceSeg203_01 chain
  [(0x8000e368#64, 0xfb010113#32),
   (0x8000e36c#64, 0x3213823#32),
   (0x8000e370#64, 0x3313423#32),
   (0x8000e374#64, 0x3413023#32),
   (0x8000e378#64, 0x1513c23#32),
   (0x8000e37c#64, 0x1613823#32),
   (0x8000e380#64, 0x1713423#32),
   (0x8000e384#64, 0x4113423#32)]

def traceLds203_01 : List (List (BitVec 8)) :=
  []

theorem facts203_01 : ChainFacts (writeLog snapshotMem traceD203_01.log)
    (writeLog snapshotMem traceD203_01.log) traceD203_01.regs traceLds203_01 traceSeg203_01 := by
  have kind0 : (mkLine 0x8000e368#64 0xfb010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e36c#64 0x3213823#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000e370#64 0x3313423#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000e374#64 0x3413023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000e378#64 0x1513c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x8000e37c#64 0x1613823#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000e380#64 0x1713423#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x8000e384#64 0x4113423#32).kind = MKind.sd := by decide
  simp only [traceSeg203_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01513c23
    | exact DecodeTable.decode_01613823
    | exact DecodeTable.decode_01713423
    | exact DecodeTable.decode_03213823
    | exact DecodeTable.decode_03313423
    | exact DecodeTable.decode_03413023
    | exact DecodeTable.decode_04113423
    | exact DecodeTable.decode_fb010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_01 {c : Config} (h : TraceHolds traceD203_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_01 traceLds203_01 (by decide) facts203_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 219 ++ (evalBlocks traceSeg203_01 (SegEvalState.init traceD203_01.regs traceLds203_01)).log = traceStores.take 226
  have hw : (evalBlocks traceSeg203_01 (SegEvalState.init traceD203_01.regs traceLds203_01)).log = (traceStores.drop 219).take 7 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_01

#derive_case traceSeg203_02 chain
  [(0x8000e388#64, 0x4813023#32),
   (0x8000e38c#64, 0x2913c23#32),
   (0x8000e390#64, 0x60913#32),
   (0x8000e394#64, 0x50a13#32),
   (0x8000e398#64, 0x58a93#32),
   (0x8000e39c#64, 0xb13#32),
   (0x8000e3a0#64, 0x100b93#32),
   (0x8000e3a4#64, 0xfff00993#32)]

def traceLds203_02 : List (List (BitVec 8)) :=
  []

theorem facts203_02 : ChainFacts (writeLog snapshotMem traceD203_02.log)
    (writeLog snapshotMem traceD203_02.log) traceD203_02.regs traceLds203_02 traceSeg203_02 := by
  have kind0 : (mkLine 0x8000e388#64 0x4813023#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000e38c#64 0x2913c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000e390#64 0x60913#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000e394#64 0x50a13#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000e398#64 0x58a93#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x8000e39c#64 0xb13#32).kind = MKind.addi := by decide
  have kind6 : (mkLine 0x8000e3a0#64 0x100b93#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000e3a4#64 0xfff00993#32).kind = MKind.addi := by decide
  simp only [traceSeg203_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000b13
    | exact DecodeTable.decode_00050a13
    | exact DecodeTable.decode_00058a93
    | exact DecodeTable.decode_00060913
    | exact DecodeTable.decode_00100b93
    | exact DecodeTable.decode_02913c23
    | exact DecodeTable.decode_04813023
    | exact DecodeTable.decode_fff00993
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_02 {c : Config} (h : TraceHolds traceD203_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_02 traceLds203_02 (by decide) facts203_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 226 ++ (evalBlocks traceSeg203_02 (SegEvalState.init traceD203_02.regs traceLds203_02)).log = traceStores.take 228
  have hw : (evalBlocks traceSeg203_02 (SegEvalState.init traceD203_02.regs traceLds203_02)).log = (traceStores.drop 226).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_02

#derive_case traceSeg203_03 chain
  [(0x8000e3a8#64, 0x892783#32)]
    terminator ⟨0x8000e3ac#64, 0x04f05a63#32, 0x63#8, 0x5a#8, 0xf0#8, 0x04#8, .br bop.BGE false, 0, 15, 0x0054#13, 0#21, 0#12⟩

def traceLds203_03 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts203_03 : ChainFacts (writeLog snapshotMem traceD203_03.log)
    (writeLog snapshotMem traceD203_03.log) traceD203_03.regs traceLds203_03 traceSeg203_03 := by
  have kind0 : (mkLine 0x8000e3a8#64 0x892783#32).kind = MKind.lw := by decide
  simp only [traceSeg203_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00892783
    | exact DecodeTable.decode_04f05a63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_03 {c : Config} (h : TraceHolds traceD203_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_03 traceLds203_03 (by decide) facts203_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 228 ++ (evalBlocks traceSeg203_03 (SegEvalState.init traceD203_03.regs traceLds203_03)).log = traceStores.take 228
  have hw : (evalBlocks traceSeg203_03 (SegEvalState.init traceD203_03.regs traceLds203_03)).log = (traceStores.drop 228).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_03

#derive_case traceSeg203_04 chain
  [(0x8000e3b0#64, 0x2079793#32),
   (0x8000e3b4#64, 0x207d793#32),
   (0x8000e3b8#64, 0x179493#32),
   (0x8000e3bc#64, 0xf484b3#32),
   (0x8000e3c0#64, 0x1093403#32),
   (0x8000e3c4#64, 0x349493#32),
   (0x8000e3c8#64, 0x40f484b3#32),
   (0x8000e3cc#64, 0x349493#32)]

def traceLds203_04 : List (List (BitVec 8)) :=
  [[0x68#8, 0xba#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts203_04 : ChainFacts (writeLog snapshotMem traceD203_04.log)
    (writeLog snapshotMem traceD203_04.log) traceD203_04.regs traceLds203_04 traceSeg203_04 := by
  have kind0 : (mkLine 0x8000e3b0#64 0x2079793#32).kind = MKind.slli := by decide
  have kind1 : (mkLine 0x8000e3b4#64 0x207d793#32).kind = MKind.srli := by decide
  have kind2 : (mkLine 0x8000e3b8#64 0x179493#32).kind = MKind.slli := by decide
  have kind3 : (mkLine 0x8000e3bc#64 0xf484b3#32).kind = MKind.add := by decide
  have kind4 : (mkLine 0x8000e3c0#64 0x1093403#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000e3c4#64 0x349493#32).kind = MKind.slli := by decide
  have kind6 : (mkLine 0x8000e3c8#64 0x40f484b3#32).kind = MKind.sub := by decide
  have kind7 : (mkLine 0x8000e3cc#64 0x349493#32).kind = MKind.slli := by decide
  simp only [traceSeg203_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00179493
    | exact DecodeTable.decode_00349493
    | exact DecodeTable.decode_00f484b3
    | exact DecodeTable.decode_01093403
    | exact DecodeTable.decode_02079793
    | exact DecodeTable.decode_0207d793
    | exact DecodeTable.decode_40f484b3
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_04 {c : Config} (h : TraceHolds traceD203_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_04 traceLds203_04 (by decide) facts203_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 228 ++ (evalBlocks traceSeg203_04 (SegEvalState.init traceD203_04.regs traceLds203_04)).log = traceStores.take 228
  have hw : (evalBlocks traceSeg203_04 (SegEvalState.init traceD203_04.regs traceLds203_04)).log = (traceStores.drop 228).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_04

#derive_case traceSeg203_05 chain
  [(0x8000e3d0#64, 0x9404b3#32),
   (0x8000e3d4#64, 0x1045783#32)]
    terminator ⟨0x8000e3d8#64, 0x02fbf063#32, 0x63#8, 0xf0#8, 0xfb#8, 0x02#8, .br bop.BGEU false, 23, 15, 0x0020#13, 0#21, 0#12⟩

def traceLds203_05 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8]]

theorem facts203_05 : ChainFacts (writeLog snapshotMem traceD203_05.log)
    (writeLog snapshotMem traceD203_05.log) traceD203_05.regs traceLds203_05 traceSeg203_05 := by
  have kind0 : (mkLine 0x8000e3d0#64 0x9404b3#32).kind = MKind.add := by decide
  have kind1 : (mkLine 0x8000e3d4#64 0x1045783#32).kind = MKind.lhu := by decide
  simp only [traceSeg203_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_009404b3
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_02fbf063
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_05 {c : Config} (h : TraceHolds traceD203_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD203_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_05 traceLds203_05 (by decide) facts203_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 228 ++ (evalBlocks traceSeg203_05 (SegEvalState.init traceD203_05.regs traceLds203_05)).log = traceStores.take 228
  have hw : (evalBlocks traceSeg203_05 (SegEvalState.init traceD203_05.regs traceLds203_05)).log = (traceStores.drop 228).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_05

#derive_case traceSeg203_06 chain
  [(0x8000e3dc#64, 0x1241783#32),
   (0x8000e3e0#64, 0x40593#32),
   (0x8000e3e4#64, 0xa0513#32)]
    terminator ⟨0x8000e3e8#64, 0x01378863#32, 0x63#8, 0x88#8, 0x37#8, 0x01#8, .br bop.BEQ false, 15, 19, 0x0010#13, 0#21, 0#12⟩

def traceLds203_06 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8]]

theorem facts203_06 : ChainFacts (writeLog snapshotMem traceD203_06.log)
    (writeLog snapshotMem traceD203_06.log) traceD203_06.regs traceLds203_06 traceSeg203_06 := by
  have kind0 : (mkLine 0x8000e3dc#64 0x1241783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000e3e0#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000e3e4#64 0xa0513#32).kind = MKind.addi := by decide
  simp only [traceSeg203_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00040593
    | exact DecodeTable.decode_000a0513
    | exact DecodeTable.decode_01241783
    | exact DecodeTable.decode_01378863
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run203_06 {c : Config} (h : TraceHolds traceD203_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD204 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg203_06 traceLds203_06 (by decide) facts203_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 228 ++ (evalBlocks traceSeg203_06 (SegEvalState.init traceD203_06.regs traceLds203_06)).log = traceStores.take 228
  have hw : (evalBlocks traceSeg203_06 (SegEvalState.init traceD203_06.regs traceLds203_06)).log = (traceStores.drop 228).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run203_06
theorem run203 {c : Config} (h : TraceHolds traceD203 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD204 c' := by
  obtain ⟨c0, s0, h0⟩ := run203_00 h
  obtain ⟨c1, s1, h1⟩ := run203_01 h0
  obtain ⟨c2, s2, h2⟩ := run203_02 h1
  obtain ⟨c3, s3, h3⟩ := run203_03 h2
  obtain ⟨c4, s4, h4⟩ := run203_04 h3
  obtain ⟨c5, s5, h5⟩ := run203_05 h4
  obtain ⟨c6, s6, h6⟩ := run203_06 h5
  exact ⟨c6, ((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6, h6⟩

#print axioms run203
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts204 : TraceCallFacts traceD204 0xa80e7#32
    (instruction.JALR (0x0#12, gprIdx 21, gprIdx 1)) 0xe7#8 0x80#8 0xa#8 0x0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_000a80e7

theorem run204 {c : Config} (h : TraceHolds traceD204 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0xa80e7#32 0x0#12 21 0x8000e9f8#64
    0xe7#8 0x80#8 0xa#8 0x0#8 facts204
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run204
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD205_01 : TraceData :=
  { pc := 0x8000ea08#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001bc90#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 230,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD205_02 : TraceData :=
  { pc := 0x8000ea1c#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 232,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD205_03 : TraceData :=
  { pc := 0x8000ea24#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x80005d2c#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 232,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD205_04 : TraceData :=
  { pc := 0x8000ea34#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0x4#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 232,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD205_05 : TraceData :=
  { pc := 0x8000eb28#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0x0#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 232,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg205_00 chain
  [(0x8000e9f8#64, 0xfe010113#32),
   (0x8000e9fc#64, 0x113c23#32),
   (0x8000ea00#64, 0x1213023#32)]
    terminator ⟨0x8000ea04#64, 0x0e058263#32, 0x63#8, 0x82#8, 0x05#8, 0x0e#8, .br bop.BEQ false, 11, 0, 0x00e4#13, 0#21, 0#12⟩

def traceLds205_00 : List (List (BitVec 8)) :=
  []

theorem facts205_00 : ChainFacts (writeLog snapshotMem traceD205.log)
    (writeLog snapshotMem traceD205.log) traceD205.regs traceLds205_00 traceSeg205_00 := by
  have kind0 : (mkLine 0x8000e9f8#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e9fc#64 0x113c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea00#64 0x1213023#32).kind = MKind.sd := by decide
  simp only [traceSeg205_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00113c23
    | exact DecodeTable.decode_fe010113
    | exact OutputAliasDecode.decode_01213023
    | exact OutputAliasDecode.decode_0e058263
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_00 {c : Config} (h : TraceHolds traceD205 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_00 traceLds205_00 (by decide) facts205_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 228 ++ (evalBlocks traceSeg205_00 (SegEvalState.init traceD205.regs traceLds205_00)).log = traceStores.take 230
  have hw : (evalBlocks traceSeg205_00 (SegEvalState.init traceD205.regs traceLds205_00)).log = (traceStores.drop 228).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_00

#derive_case traceSeg205_01 chain
  [(0x8000ea08#64, 0x813823#32),
   (0x8000ea0c#64, 0x913423#32),
   (0x8000ea10#64, 0x58413#32),
   (0x8000ea14#64, 0x50493#32)]
    terminator ⟨0x8000ea18#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds205_01 : List (List (BitVec 8)) :=
  []

theorem facts205_01 : ChainFacts (writeLog snapshotMem traceD205_01.log)
    (writeLog snapshotMem traceD205_01.log) traceD205_01.regs traceLds205_01 traceSeg205_01 := by
  have kind0 : (mkLine 0x8000ea08#64 0x813823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ea0c#64 0x913423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea10#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ea14#64 0x50493#32).kind = MKind.addi := by decide
  simp only [traceSeg205_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00050663
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00813823
    | exact OutputAliasDecode.decode_00913423
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_01 {c : Config} (h : TraceHolds traceD205_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_01 traceLds205_01 (by decide) facts205_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 230 ++ (evalBlocks traceSeg205_01 (SegEvalState.init traceD205_01.regs traceLds205_01)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg205_01 (SegEvalState.init traceD205_01.regs traceLds205_01)).log = (traceStores.drop 230).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_01

#derive_case traceSeg205_02 chain
  [(0x8000ea1c#64, 0x4853783#32)]
    terminator ⟨0x8000ea20#64, 0x10078063#32, 0x63#8, 0x80#8, 0x07#8, 0x10#8, .br bop.BEQ false, 15, 0, 0x0100#13, 0#21, 0#12⟩

def traceLds205_02 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts205_02 : ChainFacts (writeLog snapshotMem traceD205_02.log)
    (writeLog snapshotMem traceD205_02.log) traceD205_02.regs traceLds205_02 traceSeg205_02 := by
  have kind0 : (mkLine 0x8000ea1c#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg205_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact OutputAliasDecode.decode_10078063
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_02 {c : Config} (h : TraceHolds traceD205_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_02 traceLds205_02 (by decide) facts205_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg205_02 (SegEvalState.init traceD205_02.regs traceLds205_02)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg205_02 (SegEvalState.init traceD205_02.regs traceLds205_02)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_02

#derive_case traceSeg205_03 chain
  [(0x8000ea24#64, 0xb042783#32),
   (0x8000ea28#64, 0x1041703#32),
   (0x8000ea2c#64, 0x17f793#32)]
    terminator ⟨0x8000ea30#64, 0x0a079663#32, 0x63#8, 0x96#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00ac#13, 0#21, 0#12⟩

def traceLds205_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x4#8, 0x0#8]]

theorem facts205_03 : ChainFacts (writeLog snapshotMem traceD205_03.log)
    (writeLog snapshotMem traceD205_03.log) traceD205_03.regs traceLds205_03 traceSeg205_03 := by
  have kind0 : (mkLine 0x8000ea24#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000ea28#64 0x1041703#32).kind = MKind.lh := by decide
  have kind2 : (mkLine 0x8000ea2c#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg205_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_01041703
    | exact DecodeTable.decode_0b042783
    | exact OutputAliasDecode.decode_0a079663
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_03 {c : Config} (h : TraceHolds traceD205_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_03 traceLds205_03 (by decide) facts205_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg205_03 (SegEvalState.init traceD205_03.regs traceLds205_03)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg205_03 (SegEvalState.init traceD205_03.regs traceLds205_03)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_03

#derive_case traceSeg205_04 chain
  [(0x8000ea34#64, 0x20077713#32)]
    terminator ⟨0x8000ea38#64, 0x0e070863#32, 0x63#8, 0x08#8, 0x07#8, 0x0e#8, .br bop.BEQ true, 14, 0, 0x00f0#13, 0#21, 0#12⟩

def traceLds205_04 : List (List (BitVec 8)) :=
  []

theorem facts205_04 : ChainFacts (writeLog snapshotMem traceD205_04.log)
    (writeLog snapshotMem traceD205_04.log) traceD205_04.regs traceLds205_04 traceSeg205_04 := by
  have kind0 : (mkLine 0x8000ea34#64 0x20077713#32).kind = MKind.andi := by decide
  simp only [traceSeg205_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_20077713
    | exact OutputAliasDecode.decode_0e070863
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_04 {c : Config} (h : TraceHolds traceD205_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD205_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_04 traceLds205_04 (by decide) facts205_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg205_04 (SegEvalState.init traceD205_04.regs traceLds205_04)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg205_04 (SegEvalState.init traceD205_04.regs traceLds205_04)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_04

#derive_case traceSeg205_05 chain
  [(0x8000eb28#64, 0xa043503#32)]

def traceLds205_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts205_05 : ChainFacts (writeLog snapshotMem traceD205_05.log)
    (writeLog snapshotMem traceD205_05.log) traceD205_05.regs traceLds205_05 traceSeg205_05 := by
  have kind0 : (mkLine 0x8000eb28#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg205_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run205_05 {c : Config} (h : TraceHolds traceD205_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD206 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg205_05 traceLds205_05 (by decide) facts205_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg205_05 (SegEvalState.init traceD205_05.regs traceLds205_05)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg205_05 (SegEvalState.init traceD205_05.regs traceLds205_05)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run205_05
theorem run205 {c : Config} (h : TraceHolds traceD205 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD206 c' := by
  obtain ⟨c0, s0, h0⟩ := run205_00 h
  obtain ⟨c1, s1, h1⟩ := run205_01 h0
  obtain ⟨c2, s2, h2⟩ := run205_02 h1
  obtain ⟨c3, s3, h3⟩ := run205_03 h2
  obtain ⟨c4, s4, h4⟩ := run205_04 h3
  obtain ⟨c5, s5, h5⟩ := run205_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run205
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts206 : TraceCallFacts traceD206 0xcb4f80ef#32
    (instruction.JAL (0x1f84b4#21, gprIdx 1)) 0xef#8 0x80#8 0x4f#8 0xcb#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := OutputAliasDecode.decode_cb4f80ef

theorem run206 {c : Config} (h : TraceHolds traceD206 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD207 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xcb4f80ef#32 0x1f84b4#21 0xef#8 0x80#8 0x4f#8 0xcb#8 facts206 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run206
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg207 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds207 : List (List (BitVec 8)) :=
  []

theorem facts207 : ChainFacts (writeLog snapshotMem traceD207.log)
    (writeLog snapshotMem traceD207.log) traceD207.regs traceLds207 traceSeg207 := by
  simp only [traceSeg207, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run207 {c : Config} (h : TraceHolds traceD207 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD208 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg207 traceLds207 (by decide) facts207 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg207 (SegEvalState.init traceD207.regs traceLds207)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg207 (SegEvalState.init traceD207.regs traceLds207)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run207
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg208 chain
  [(0x8000eb30#64, 0x1041783#32)]
    terminator ⟨0x8000eb34#64, 0xf00794e3#32, 0xe3#8, 0x94#8, 0x07#8, 0xf0#8, .br bop.BNE true, 15, 0, 0x1f08#13, 0#21, 0#12⟩ ;;
  [(0x8000ea3c#64, 0x40593#32),
   (0x8000ea40#64, 0x48513#32)]

def traceLds208 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8]]

theorem facts208 : ChainFacts (writeLog snapshotMem traceD208.log)
    (writeLog snapshotMem traceD208.log) traceD208.regs traceLds208 traceSeg208 := by
  have kind0 : (mkLine 0x8000eb30#64 0x1041783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000ea3c#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea40#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg208, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00040593
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_01041783
    | exact OutputAliasDecode.decode_f00794e3
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run208 {c : Config} (h : TraceHolds traceD208 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD209 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg208 traceLds208 (by decide) facts208 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg208 (SegEvalState.init traceD208.regs traceLds208)).log = traceStores.take 232
  have hw : (evalBlocks traceSeg208 (SegEvalState.init traceD208.regs traceLds208)).log = (traceStores.drop 232).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run208
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts209 : TraceCallFacts traceD209 0x12c000ef#32
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

theorem run209 {c : Config} (h : TraceHolds traceD209 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x12c000ef#32 0x12c#21 0xef#8 0x0#8 0xc0#8 0x12#8 facts209 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run209
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD210_01 : TraceData :=
  { pc := 0x8000eb80#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0x4#64), (15, 0x4#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 234,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_02 : TraceData :=
  { pc := 0x8000eb94#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x8001bb98#64), (14, 0x4#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 235,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_03 : TraceData :=
  { pc := 0x8000eba4#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x804#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 235,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_04 : TraceData :=
  { pc := 0x8000ed40#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x804#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 236,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_05 : TraceData :=
  { pc := 0x8000ed48#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x804#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 236,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_06 : TraceData :=
  { pc := 0x8000ec9c#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x804#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 236,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD210_07 : TraceData :=
  { pc := 0x8000ecac#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001ba68#64), (9, 0x8001b538#64), (10, 0x0#64), (11, 0x8001ba68#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x804#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 236,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg210_00 chain
  [(0x8000eb70#64, 0x1059703#32),
   (0x8000eb74#64, 0xfd010113#32),
   (0x8000eb78#64, 0x2813023#32),
   (0x8000eb7c#64, 0x1313423#32)]

def traceLds210_00 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8]]

theorem facts210_00 : ChainFacts (writeLog snapshotMem traceD210.log)
    (writeLog snapshotMem traceD210.log) traceD210.regs traceLds210_00 traceSeg210_00 := by
  have kind0 : (mkLine 0x8000eb70#64 0x1059703#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000eb74#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb78#64 0x2813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000eb7c#64 0x1313423#32).kind = MKind.sd := by decide
  simp only [traceSeg210_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run210_00 {c : Config} (h : TraceHolds traceD210 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_00 traceLds210_00 (by decide) facts210_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 232 ++ (evalBlocks traceSeg210_00 (SegEvalState.init traceD210.regs traceLds210_00)).log = traceStores.take 234
  have hw : (evalBlocks traceSeg210_00 (SegEvalState.init traceD210.regs traceLds210_00)).log = (traceStores.drop 232).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_00

#derive_case traceSeg210_01 chain
  [(0x8000eb80#64, 0x2113423#32),
   (0x8000eb84#64, 0x877793#32),
   (0x8000eb88#64, 0x58413#32),
   (0x8000eb8c#64, 0x50993#32)]
    terminator ⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE false, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds210_01 : List (List (BitVec 8)) :=
  []

theorem facts210_01 : ChainFacts (writeLog snapshotMem traceD210_01.log)
    (writeLog snapshotMem traceD210_01.log) traceD210_01.regs traceLds210_01 traceSeg210_01 := by
  have kind0 : (mkLine 0x8000eb80#64 0x2113423#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000eb84#64 0x877793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000eb88#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000eb8c#64 0x50993#32).kind = MKind.addi := by decide
  simp only [traceSeg210_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run210_01 {c : Config} (h : TraceHolds traceD210_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_01 traceLds210_01 (by decide) facts210_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 234 ++ (evalBlocks traceSeg210_01 (SegEvalState.init traceD210_01.regs traceLds210_01)).log = traceStores.take 235
  have hw : (evalBlocks traceSeg210_01 (SegEvalState.init traceD210_01.regs traceLds210_01)).log = (traceStores.drop 234).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_01

#derive_case traceSeg210_02 chain
  [(0x8000eb94#64, 0x17b7#32),
   (0x8000eb98#64, 0x80078793#32),
   (0x8000eb9c#64, 0x85a683#32),
   (0x8000eba0#64, 0xf767b3#32)]

def traceLds210_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts210_02 : ChainFacts (writeLog snapshotMem traceD210_02.log)
    (writeLog snapshotMem traceD210_02.log) traceD210_02.regs traceLds210_02 traceSeg210_02 := by
  have kind0 : (mkLine 0x8000eb94#64 0x17b7#32).kind = MKind.lui := by decide
  have kind1 : (mkLine 0x8000eb98#64 0x80078793#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb9c#64 0x85a683#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000eba0#64 0xf767b3#32).kind = MKind.or := by decide
  simp only [traceSeg210_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run210_02 {c : Config} (h : TraceHolds traceD210_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_02 traceLds210_02 (by decide) facts210_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 235 ++ (evalBlocks traceSeg210_02 (SegEvalState.init traceD210_02.regs traceLds210_02)).log = traceStores.take 235
  have hw : (evalBlocks traceSeg210_02 (SegEvalState.init traceD210_02.regs traceLds210_02)).log = (traceStores.drop 235).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_02

#derive_case traceSeg210_03 chain
  [(0x8000eba4#64, 0xf59823#32)]
    terminator ⟨0x8000eba8#64, 0x18d05c63#32, 0x63#8, 0x5c#8, 0xd0#8, 0x18#8, .br bop.BGE true, 0, 13, 0x0198#13, 0#21, 0#12⟩

def traceLds210_03 : List (List (BitVec 8)) :=
  []

theorem facts210_03 : ChainFacts (writeLog snapshotMem traceD210_03.log)
    (writeLog snapshotMem traceD210_03.log) traceD210_03.regs traceLds210_03 traceSeg210_03 := by
  have kind0 : (mkLine 0x8000eba4#64 0xf59823#32).kind = MKind.sh := by decide
  simp only [traceSeg210_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00f59823
    | exact DecodeTable.decode_18d05c63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run210_03 {c : Config} (h : TraceHolds traceD210_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_03 traceLds210_03 (by decide) facts210_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 235 ++ (evalBlocks traceSeg210_03 (SegEvalState.init traceD210_03.regs traceLds210_03)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg210_03 (SegEvalState.init traceD210_03.regs traceLds210_03)).log = (traceStores.drop 235).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_03

#derive_case traceSeg210_04 chain
  [(0x8000ed40#64, 0x705a683#32)]
    terminator ⟨0x8000ed44#64, 0xe6d044e3#32, 0xe3#8, 0x44#8, 0xd0#8, 0xe6#8, .br bop.BLT false, 0, 13, 0x1e68#13, 0#21, 0#12⟩

def traceLds210_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts210_04 : ChainFacts (writeLog snapshotMem traceD210_04.log)
    (writeLog snapshotMem traceD210_04.log) traceD210_04.regs traceLds210_04 traceSeg210_04 := by
  have kind0 : (mkLine 0x8000ed40#64 0x705a683#32).kind = MKind.lw := by decide
  simp only [traceSeg210_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0705a683
    | exact DecodeTable.decode_e6d044e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run210_04 {c : Config} (h : TraceHolds traceD210_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_04 traceLds210_04 (by decide) facts210_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg210_04 (SegEvalState.init traceD210_04.regs traceLds210_04)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg210_04 (SegEvalState.init traceD210_04.regs traceLds210_04)).log = (traceStores.drop 236).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_04

#derive_case traceSeg210_05 chain
  []
    terminator ⟨0x8000ed48#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0#13, 0x1fff54#21, 0#12⟩

def traceLds210_05 : List (List (BitVec 8)) :=
  []

theorem facts210_05 : ChainFacts (writeLog snapshotMem traceD210_05.log)
    (writeLog snapshotMem traceD210_05.log) traceD210_05.regs traceLds210_05 traceSeg210_05 := by
  simp only [traceSeg210_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_f55ff06f
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run210_05 {c : Config} (h : TraceHolds traceD210_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_05 traceLds210_05 (by decide) facts210_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg210_05 (SegEvalState.init traceD210_05.regs traceLds210_05)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg210_05 (SegEvalState.init traceD210_05.regs traceLds210_05)).log = (traceStores.drop 236).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_05

#derive_case traceSeg210_06 chain
  [(0x8000ec9c#64, 0x2813083#32),
   (0x8000eca0#64, 0x2013403#32),
   (0x8000eca4#64, 0x813983#32),
   (0x8000eca8#64, 0x513#32)]

def traceLds210_06 : List (List (BitVec 8)) :=
  [[0x48#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x68#8, 0xba#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8]]

theorem facts210_06 : ChainFacts (writeLog snapshotMem traceD210_06.log)
    (writeLog snapshotMem traceD210_06.log) traceD210_06.regs traceLds210_06 traceSeg210_06 := by
  have kind0 : (mkLine 0x8000ec9c#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eca0#64 0x2013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eca4#64 0x813983#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eca8#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg210_06, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run210_06 {c : Config} (h : TraceHolds traceD210_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD210_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_06 traceLds210_06 (by decide) facts210_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg210_06 (SegEvalState.init traceD210_06.regs traceLds210_06)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg210_06 (SegEvalState.init traceD210_06.regs traceLds210_06)).log = (traceStores.drop 236).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_06

#derive_case traceSeg210_07 chain
  [(0x8000ecac#64, 0x3010113#32)]
    terminator ⟨0x8000ecb0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds210_07 : List (List (BitVec 8)) :=
  []

theorem facts210_07 : ChainFacts (writeLog snapshotMem traceD210_07.log)
    (writeLog snapshotMem traceD210_07.log) traceD210_07.regs traceLds210_07 traceSeg210_07 := by
  have kind0 : (mkLine 0x8000ecac#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg210_07, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_03010113
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run210_07 {c : Config} (h : TraceHolds traceD210_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD211 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg210_07 traceLds210_07 (by decide) facts210_07 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg210_07 (SegEvalState.init traceD210_07.regs traceLds210_07)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg210_07 (SegEvalState.init traceD210_07.regs traceLds210_07)).log = (traceStores.drop 236).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run210_07
theorem run210 {c : Config} (h : TraceHolds traceD210 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD211 c' := by
  obtain ⟨c0, s0, h0⟩ := run210_00 h
  obtain ⟨c1, s1, h1⟩ := run210_01 h0
  obtain ⟨c2, s2, h2⟩ := run210_02 h1
  obtain ⟨c3, s3, h3⟩ := run210_03 h2
  obtain ⟨c4, s4, h4⟩ := run210_04 h3
  obtain ⟨c5, s5, h5⟩ := run210_05 h4
  obtain ⟨c6, s6, h6⟩ := run210_06 h5
  obtain ⟨c7, s7, h7⟩ := run210_07 h6
  exact ⟨c7, (((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7, h7⟩

#print axioms run210
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg211 chain
  [(0x8000ea48#64, 0x5043783#32),
   (0x8000ea4c#64, 0x50913#32)]
    terminator ⟨0x8000ea50#64, 0x00078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8000ea54#64, 0x3043583#32),
   (0x8000ea58#64, 0x48513#32)]

def traceLds211 : List (List (BitVec 8)) :=
  [[0xc0#8, 0xf0#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x68#8, 0xba#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts211 : ChainFacts (writeLog snapshotMem traceD211.log)
    (writeLog snapshotMem traceD211.log) traceD211.regs traceLds211 traceSeg211 := by
  have kind0 : (mkLine 0x8000ea48#64 0x5043783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ea4c#64 0x50913#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea54#64 0x3043583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea58#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg211, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run211 {c : Config} (h : TraceHolds traceD211 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD212 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg211 traceLds211 (by decide) facts211 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg211 (SegEvalState.init traceD211.regs traceLds211)).log = traceStores.take 236
  have hw : (evalBlocks traceSeg211 (SegEvalState.init traceD211.regs traceLds211)).log = (traceStores.drop 236).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run211
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts212 : TraceCallFacts traceD212 0x780e7#32
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

theorem run212 {c : Config} (h : TraceHolds traceD212 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD213 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x8000f0c0#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts212
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run212
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg213 chain
  [(0x8000f0c0#64, 0x1259583#32)]
    terminator ⟨0x8000f0c4#64, 0x1a40106f#32, 0x6f#8, 0x10#8, 0x40#8, 0x1a#8, .j, 0, 0, 0#13, 0x0011a4#21, 0#12⟩ ;;
  [(0x80010268#64, 0xff010113#32),
   (0x8001026c#64, 0x813023#32),
   (0x80010270#64, 0x50413#32),
   (0x80010274#64, 0x58513#32),
   (0x80010278#64, 0x4e01ac23#32),
   (0x8001027c#64, 0x113423#32)]

def traceLds213 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8]]

theorem facts213 : ChainFacts (writeLog snapshotMem traceD213.log)
    (writeLog snapshotMem traceD213.log) traceD213.regs traceLds213 traceSeg213 := by
  have kind0 : (mkLine 0x8000f0c0#64 0x1259583#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x80010268#64 0xff010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8001026c#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80010270#64 0x50413#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80010274#64 0x58513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80010278#64 0x4e01ac23#32).kind = MKind.sw := by decide
  have kind6 : (mkLine 0x8001027c#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg213, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run213 {c : Config} (h : TraceHolds traceD213 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD214 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg213 traceLds213 (by decide) facts213 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 236 ++ (evalBlocks traceSeg213 (SegEvalState.init traceD213.regs traceLds213)).log = traceStores.take 239
  have hw : (evalBlocks traceSeg213 (SegEvalState.init traceD213.regs traceLds213)).log = (traceStores.drop 236).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run213
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts214 : TraceCallFacts traceD214 0xe19ef0ef#32
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

theorem run214 {c : Config} (h : TraceHolds traceD214 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD215 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe19ef0ef#32 0x1efe18#21 0xef#8 0xf0#8 0x9e#8 0xe1#8 facts214 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run214
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg215 chain
  [(0x80000098#64, 0x513#32)]
    terminator ⟨0x8000009c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds215 : List (List (BitVec 8)) :=
  []

theorem facts215 : ChainFacts (writeLog snapshotMem traceD215.log)
    (writeLog snapshotMem traceD215.log) traceD215.regs traceLds215 traceSeg215 := by
  have kind0 : (mkLine 0x80000098#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg215, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run215 {c : Config} (h : TraceHolds traceD215 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD216 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg215 traceLds215 (by decide) facts215 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 239 ++ (evalBlocks traceSeg215 (SegEvalState.init traceD215.regs traceLds215)).log = traceStores.take 239
  have hw : (evalBlocks traceSeg215 (SegEvalState.init traceD215.regs traceLds215)).log = (traceStores.drop 239).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run215
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg216 chain
  [(0x80010284#64, 0xfff00793#32)]
    terminator ⟨0x80010288#64, 0x00f50a63#32, 0x63#8, 0x0a#8, 0xf5#8, 0x00#8, .br bop.BEQ false, 10, 15, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8001028c#64, 0x813083#32),
   (0x80010290#64, 0x13403#32),
   (0x80010294#64, 0x1010113#32)]
    terminator ⟨0x80010298#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds216 : List (List (BitVec 8)) :=
  [[0x60#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x68#8, 0xba#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts216 : ChainFacts (writeLog snapshotMem traceD216.log)
    (writeLog snapshotMem traceD216.log) traceD216.regs traceLds216 traceSeg216 := by
  have kind0 : (mkLine 0x80010284#64 0xfff00793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8001028c#64 0x813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80010290#64 0x13403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80010294#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg216, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run216 {c : Config} (h : TraceHolds traceD216 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD217 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg216 traceLds216 (by decide) facts216 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 239 ++ (evalBlocks traceSeg216 (SegEvalState.init traceD216.regs traceLds216)).log = traceStores.take 239
  have hw : (evalBlocks traceSeg216 (SegEvalState.init traceD216.regs traceLds216)).log = (traceStores.drop 239).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run216
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg217 chain
  []
    terminator ⟨0x8000ea60#64, 0x0a054063#32, 0x63#8, 0x40#8, 0x05#8, 0x0a#8, .br bop.BLT false, 10, 0, 0x00a0#13, 0#21, 0#12⟩ ;;
  [(0x8000ea64#64, 0x1045783#32),
   (0x8000ea68#64, 0x807f793#32)]
    terminator ⟨0x8000ea6c#64, 0x0a079263#32, 0x63#8, 0x92#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00a4#13, 0#21, 0#12⟩ ;;
  [(0x8000ea70#64, 0x5843583#32)]
    terminator ⟨0x8000ea74#64, 0x00058c63#32, 0x63#8, 0x8c#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x8000ea8c#64, 0x7843583#32)]
    terminator ⟨0x8000ea90#64, 0x00058863#32, 0x63#8, 0x88#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0010#13, 0#21, 0#12⟩

def traceLds217 : List (List (BitVec 8)) :=
  [[0x4#8, 0x8#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts217 : ChainFacts (writeLog snapshotMem traceD217.log)
    (writeLog snapshotMem traceD217.log) traceD217.regs traceLds217 traceSeg217 := by
  have kind0 : (mkLine 0x8000ea64#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind1 : (mkLine 0x8000ea68#64 0x807f793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000ea70#64 0x5843583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea8c#64 0x7843583#32).kind = MKind.ld := by decide
  simp only [traceSeg217, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run217 {c : Config} (h : TraceHolds traceD217 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD218 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg217 traceLds217 (by decide) facts217 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 239 ++ (evalBlocks traceSeg217 (SegEvalState.init traceD217.regs traceLds217)).log = traceStores.take 239
  have hw : (evalBlocks traceSeg217 (SegEvalState.init traceD217.regs traceLds217)).log = (traceStores.drop 239).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run217
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts218 : TraceCallFacts traceD218 0xe80f70ef#32
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

theorem run218 {c : Config} (h : TraceHolds traceD218 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD219 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe80f70ef#32 0x1f7680#21 0xef#8 0x70#8 0xf#8 0xe8#8 facts218 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run218
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg219 chain
  [(0x80006120#64, 0x4e018513#32)]
    terminator ⟨0x80006124#64, 0x6bd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6b#8, .j, 0, 0, 0#13, 0x000ebc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds219 : List (List (BitVec 8)) :=
  []

theorem facts219 : ChainFacts (writeLog snapshotMem traceD219.log)
    (writeLog snapshotMem traceD219.log) traceD219.regs traceLds219 traceSeg219 := by
  have kind0 : (mkLine 0x80006120#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg219, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6bd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run219 {c : Config} (h : TraceHolds traceD219 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD220 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg219 traceLds219 (by decide) facts219 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 239 ++ (evalBlocks traceSeg219 (SegEvalState.init traceD219.regs traceLds219)).log = traceStores.take 239
  have hw : (evalBlocks traceSeg219 (SegEvalState.init traceD219.regs traceLds219)).log = (traceStores.drop 239).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run219
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg220 chain
  [(0x8000eaa4#64, 0xb042783#32),
   (0x8000eaa8#64, 0x41823#32),
   (0x8000eaac#64, 0x17f793#32)]
    terminator ⟨0x8000eab0#64, 0x0a078463#32, 0x63#8, 0x84#8, 0x07#8, 0x0a#8, .br bop.BEQ true, 15, 0, 0x00a8#13, 0#21, 0#12⟩ ;;
  [(0x8000eb58#64, 0xa043503#32)]

def traceLds220 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts220 : ChainFacts (writeLog snapshotMem traceD220.log)
    (writeLog snapshotMem traceD220.log) traceD220.regs traceLds220 traceSeg220 := by
  have kind0 : (mkLine 0x8000eaa4#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000eaa8#64 0x41823#32).kind = MKind.sh := by decide
  have kind2 : (mkLine 0x8000eaac#64 0x17f793#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eb58#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg220, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run220 {c : Config} (h : TraceHolds traceD220 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD221 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg220 traceLds220 (by decide) facts220 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 239 ++ (evalBlocks traceSeg220 (SegEvalState.init traceD220.regs traceLds220)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg220 (SegEvalState.init traceD220.regs traceLds220)).log = (traceStores.drop 239).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run220
end Vsa.Sim.OutputAliasLoaded
