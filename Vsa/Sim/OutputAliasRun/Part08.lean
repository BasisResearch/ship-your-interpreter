import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part11
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part01
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch05Part03
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part25
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part10
import Vsa.Sim.DecodeTable.Batch07Part25
import Vsa.Sim.DecodeTable.Batch07Part28
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part14
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part20
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch13Part13
import Vsa.Sim.DecodeTable.Batch13Part22
import Vsa.Sim.DecodeTable.Batch14Part29
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part26
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.DecodeTable.Batch16Part32
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasPutchar
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts161 : TraceCallFacts traceD161 0x994f80ef#32
    (instruction.JAL (0x1f8194#21, gprIdx 1)) 0xef#8 0x80#8 0x4f#8 0x99#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_994f80ef

theorem run161 {c : Config} (h : TraceHolds traceD161 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD162 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x994f80ef#32 0x1f8194#21 0xef#8 0x80#8 0x4f#8 0x99#8 facts161 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run161
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg162 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds162 : List (List (BitVec 8)) :=
  []

theorem facts162 : ChainFacts (writeLog snapshotMem traceD162.log)
    (writeLog snapshotMem traceD162.log) traceD162.regs traceLds162 traceSeg162 := by
  simp only [traceSeg162, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run162 {c : Config} (h : TraceHolds traceD162 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD163 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg162 traceLds162 (by decide) facts162 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 193 ++ (evalBlocks traceSeg162 (SegEvalState.init traceD162.regs traceLds162)).log = traceStores.take 193
  have hw : (evalBlocks traceSeg162 (SegEvalState.init traceD162.regs traceLds162)).log = (traceStores.drop 193).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run162
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg163 chain
  [(0x8000ee50#64, 0x813703#32),
   (0x8000ee54#64, 0x13583#32)]
    terminator ⟨0x8000ee58#64, 0xfadff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xfa#8, .j, 0, 0, 0#13, 0x1fffac#21, 0#12⟩ ;;
  [(0x8000ee04#64, 0x70513#32),
   (0x8000ee08#64, 0xb13023#32)]

def traceLds163 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts163 : ChainFacts (writeLog snapshotMem traceD163.log)
    (writeLog snapshotMem traceD163.log) traceD163.regs traceLds163 traceSeg163 := by
  have kind0 : (mkLine 0x8000ee50#64 0x813703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee54#64 0x13583#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ee04#64 0x70513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ee08#64 0xb13023#32).kind = MKind.sd := by decide
  simp only [traceSeg163, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013583
    | exact DecodeTable.decode_00070513
    | exact DecodeTable.decode_00813703
    | exact DecodeTable.decode_00b13023
    | exact DecodeTable.decode_fadff06f
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run163 {c : Config} (h : TraceHolds traceD163 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD164 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg163 traceLds163 (by decide) facts163 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 193 ++ (evalBlocks traceSeg163 (SegEvalState.init traceD163.regs traceLds163)).log = traceStores.take 194
  have hw : (evalBlocks traceSeg163 (SegEvalState.init traceD163.regs traceLds163)).log = (traceStores.drop 193).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run163
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts164 : TraceCallFacts traceD164 0xd65ff0ef#32
    (instruction.JAL (0x1ffd64#21, gprIdx 1)) 0xef#8 0xf0#8 0x5f#8 0xd6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_d65ff0ef

theorem run164 {c : Config} (h : TraceHolds traceD164 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD165 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xd65ff0ef#32 0x1ffd64#21 0xef#8 0xf0#8 0x5f#8 0xd6#8 facts164 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run164
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD165_01 : TraceData :=
  { pc := 0x8000ecb4#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 197,
    out := #["\n"], payload := 0x0#4 }

def traceD165_02 : TraceData :=
  { pc := 0x8000ecc0#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 198,
    out := #["\n"], payload := 0x0#4 }

def traceD165_03 : TraceData :=
  { pc := 0x8000ece0#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 200,
    out := #["\n"], payload := 0x0#4 }

def traceD165_04 : TraceData :=
  { pc := 0x8000ecf4#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 201,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg165_00 chain
  [(0x8000eb70#64, 0x1059703#32),
   (0x8000eb74#64, 0xfd010113#32),
   (0x8000eb78#64, 0x2813023#32),
   (0x8000eb7c#64, 0x1313423#32),
   (0x8000eb80#64, 0x2113423#32),
   (0x8000eb84#64, 0x877793#32),
   (0x8000eb88#64, 0x58413#32),
   (0x8000eb8c#64, 0x50993#32)]
    terminator ⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE true, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds165_00 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts165_00 : ChainFacts (writeLog snapshotMem traceD165.log)
    (writeLog snapshotMem traceD165.log) traceD165.regs traceLds165_00 traceSeg165_00 := by
  have kind0 : (mkLine 0x8000eb70#64 0x1059703#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000eb74#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb78#64 0x2813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000eb7c#64 0x1313423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000eb80#64 0x2113423#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x8000eb84#64 0x877793#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000eb88#64 0x58413#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000eb8c#64 0x50993#32).kind = MKind.addi := by decide
  simp only [traceSeg165_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050993
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00877793
    | exact DecodeTable.decode_01059703
    | exact DecodeTable.decode_01313423
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_02813023
    | exact DecodeTable.decode_12079263
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run165_00 {c : Config} (h : TraceHolds traceD165 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD165_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg165_00 traceLds165_00 (by decide) facts165_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 194 ++ (evalBlocks traceSeg165_00 (SegEvalState.init traceD165.regs traceLds165_00)).log = traceStores.take 197
  have hw : (evalBlocks traceSeg165_00 (SegEvalState.init traceD165.regs traceLds165_00)).log = (traceStores.drop 194).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run165_00

#derive_case traceSeg165_01 chain
  [(0x8000ecb4#64, 0x1213823#32),
   (0x8000ecb8#64, 0x185b903#32)]
    terminator ⟨0x8000ecbc#64, 0x08090a63#32, 0x63#8, 0x0a#8, 0x09#8, 0x08#8, .br bop.BEQ false, 18, 0, 0x0094#13, 0#21, 0#12⟩

def traceLds165_01 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts165_01 : ChainFacts (writeLog snapshotMem traceD165_01.log)
    (writeLog snapshotMem traceD165_01.log) traceD165_01.regs traceLds165_01 traceSeg165_01 := by
  have kind0 : (mkLine 0x8000ecb4#64 0x1213823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecb8#64 0x185b903#32).kind = MKind.ld := by decide
  simp only [traceSeg165_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01213823
    | exact DecodeTable.decode_0185b903
    | exact DecodeTable.decode_08090a63
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run165_01 {c : Config} (h : TraceHolds traceD165_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD165_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg165_01 traceLds165_01 (by decide) facts165_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 197 ++ (evalBlocks traceSeg165_01 (SegEvalState.init traceD165_01.regs traceLds165_01)).log = traceStores.take 198
  have hw : (evalBlocks traceSeg165_01 (SegEvalState.init traceD165_01.regs traceLds165_01)).log = (traceStores.drop 197).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run165_01

#derive_case traceSeg165_02 chain
  [(0x8000ecc0#64, 0x913c23#32),
   (0x8000ecc4#64, 0x5b483#32),
   (0x8000ecc8#64, 0x377713#32),
   (0x8000eccc#64, 0x125b023#32),
   (0x8000ecd0#64, 0x412484bb#32),
   (0x8000ecd4#64, 0x793#32)]
    terminator ⟨0x8000ecd8#64, 0x00071463#32, 0x63#8, 0x14#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x0008#13, 0#21, 0#12⟩

def traceLds165_02 : List (List (BitVec 8)) :=
  [[0x98#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts165_02 : ChainFacts (writeLog snapshotMem traceD165_02.log)
    (writeLog snapshotMem traceD165_02.log) traceD165_02.regs traceLds165_02 traceSeg165_02 := by
  have kind0 : (mkLine 0x8000ecc0#64 0x913c23#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecc4#64 0x5b483#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ecc8#64 0x377713#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eccc#64 0x125b023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000ecd0#64 0x412484bb#32).kind = MKind.subw := by decide
  have kind5 : (mkLine 0x8000ecd4#64 0x793#32).kind = MKind.addi := by decide
  simp only [traceSeg165_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000793
    | exact DecodeTable.decode_0005b483
    | exact DecodeTable.decode_00071463
    | exact DecodeTable.decode_00377713
    | exact DecodeTable.decode_00913c23
    | exact DecodeTable.decode_0125b023
    | exact DecodeTable.decode_412484bb
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run165_02 {c : Config} (h : TraceHolds traceD165_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD165_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg165_02 traceLds165_02 (by decide) facts165_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 198 ++ (evalBlocks traceSeg165_02 (SegEvalState.init traceD165_02.regs traceLds165_02)).log = traceStores.take 200
  have hw : (evalBlocks traceSeg165_02 (SegEvalState.init traceD165_02.regs traceLds165_02)).log = (traceStores.drop 198).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run165_02

#derive_case traceSeg165_03 chain
  [(0x8000ece0#64, 0xf42623#32)]
    terminator ⟨0x8000ece4#64, 0x00904863#32, 0x63#8, 0x48#8, 0x90#8, 0x00#8, .br bop.BLT true, 0, 9, 0x0010#13, 0#21, 0#12⟩

def traceLds165_03 : List (List (BitVec 8)) :=
  []

theorem facts165_03 : ChainFacts (writeLog snapshotMem traceD165_03.log)
    (writeLog snapshotMem traceD165_03.log) traceD165_03.regs traceLds165_03 traceSeg165_03 := by
  have kind0 : (mkLine 0x8000ece0#64 0xf42623#32).kind = MKind.sw := by decide
  simp only [traceSeg165_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00904863
    | exact DecodeTable.decode_00f42623
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run165_03 {c : Config} (h : TraceHolds traceD165_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD165_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg165_03 traceLds165_03 (by decide) facts165_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 200 ++ (evalBlocks traceSeg165_03 (SegEvalState.init traceD165_03.regs traceLds165_03)).log = traceStores.take 201
  have hw : (evalBlocks traceSeg165_03 (SegEvalState.init traceD165_03.regs traceLds165_03)).log = (traceStores.drop 200).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run165_03

#derive_case traceSeg165_04 chain
  [(0x8000ecf4#64, 0x4043783#32),
   (0x8000ecf8#64, 0x3043583#32),
   (0x8000ecfc#64, 0x48693#32),
   (0x8000ed00#64, 0x90613#32),
   (0x8000ed04#64, 0x98513#32)]

def traceLds165_04 : List (List (BitVec 8)) :=
  [[0xd4#8, 0xef#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts165_04 : ChainFacts (writeLog snapshotMem traceD165_04.log)
    (writeLog snapshotMem traceD165_04.log) traceD165_04.regs traceLds165_04 traceSeg165_04 := by
  have kind0 : (mkLine 0x8000ecf4#64 0x4043783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ecf8#64 0x3043583#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ecfc#64 0x48693#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ed00#64 0x90613#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000ed04#64 0x98513#32).kind = MKind.addi := by decide
  simp only [traceSeg165_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048693
    | exact DecodeTable.decode_00090613
    | exact DecodeTable.decode_00098513
    | exact DecodeTable.decode_03043583
    | exact DecodeTable.decode_04043783
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run165_04 {c : Config} (h : TraceHolds traceD165_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD166 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg165_04 traceLds165_04 (by decide) facts165_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 201 ++ (evalBlocks traceSeg165_04 (SegEvalState.init traceD165_04.regs traceLds165_04)).log = traceStores.take 201
  have hw : (evalBlocks traceSeg165_04 (SegEvalState.init traceD165_04.regs traceLds165_04)).log = (traceStores.drop 201).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run165_04
theorem run165 {c : Config} (h : TraceHolds traceD165 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD166 c' := by
  obtain ⟨c0, s0, h0⟩ := run165_00 h
  obtain ⟨c1, s1, h1⟩ := run165_01 h0
  obtain ⟨c2, s2, h2⟩ := run165_02 h1
  obtain ⟨c3, s3, h3⟩ := run165_03 h2
  obtain ⟨c4, s4, h4⟩ := run165_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run165
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts166 : TraceCallFacts traceD166 0x780e7#32
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

theorem run166 {c : Config} (h : TraceHolds traceD166 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD167 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x8000efd4#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts166
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run166
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD167_01 : TraceData :=
  { pc := 0x8000eff8#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff630#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb97#64), (13, 0x0#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 202,
    out := #["\n"], payload := 0x0#4 }

def traceD167_02 : TraceData :=
  { pc := 0x8000f018#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff630#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x1#64), (12, 0x8001bb97#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 203,
    out := #["\n"], payload := 0x0#4 }

def traceD167_03 : TraceData :=
  { pc := 0x800104fc#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x1#64), (12, 0x8001bb97#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 203,
    out := #["\n"], payload := 0x0#4 }

def traceD167_04 : TraceData :=
  { pc := 0x8001051c#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff650#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001b538#64), (9, 0x1#64), (10, 0x1#64), (11, 0x8001bb97#64), (12, 0x1#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x1#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 205,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg167_00 chain
  [(0x8000efd4#64, 0x1059783#32),
   (0x8000efd8#64, 0xfd010113#32),
   (0x8000efdc#64, 0x68313#32),
   (0x8000efe0#64, 0x2113423#32),
   (0x8000efe4#64, 0x1007f693#32),
   (0x8000efe8#64, 0x58713#32),
   (0x8000efec#64, 0x60893#32),
   (0x8000eff0#64, 0x50813#32)]
    terminator ⟨0x8000eff4#64, 0x02069863#32, 0x63#8, 0x98#8, 0x06#8, 0x02#8, .br bop.BNE false, 13, 0, 0x0030#13, 0#21, 0#12⟩

def traceLds167_00 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts167_00 : ChainFacts (writeLog snapshotMem traceD167.log)
    (writeLog snapshotMem traceD167.log) traceD167.regs traceLds167_00 traceSeg167_00 := by
  have kind0 : (mkLine 0x8000efd4#64 0x1059783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000efd8#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000efdc#64 0x68313#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000efe0#64 0x2113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000efe4#64 0x1007f693#32).kind = MKind.andi := by decide
  have kind5 : (mkLine 0x8000efe8#64 0x58713#32).kind = MKind.addi := by decide
  have kind6 : (mkLine 0x8000efec#64 0x60893#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000eff0#64 0x50813#32).kind = MKind.addi := by decide
  simp only [traceSeg167_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050813
    | exact DecodeTable.decode_00058713
    | exact DecodeTable.decode_00060893
    | exact DecodeTable.decode_00068313
    | exact DecodeTable.decode_01059783
    | exact DecodeTable.decode_02069863
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_1007f693
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run167_00 {c : Config} (h : TraceHolds traceD167 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD167_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg167_00 traceLds167_00 (by decide) facts167_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 201 ++ (evalBlocks traceSeg167_00 (SegEvalState.init traceD167.regs traceLds167_00)).log = traceStores.take 202
  have hw : (evalBlocks traceSeg167_00 (SegEvalState.init traceD167.regs traceLds167_00)).log = (traceStores.drop 201).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run167_00

#derive_case traceSeg167_01 chain
  [(0x8000eff8#64, 0xfffff6b7#32),
   (0x8000effc#64, 0xfff68693#32),
   (0x8000f000#64, 0x2813083#32),
   (0x8000f004#64, 0xd7f7b3#32),
   (0x8000f008#64, 0x1271583#32),
   (0x8000f00c#64, 0xf71823#32),
   (0x8000f010#64, 0x30693#32),
   (0x8000f014#64, 0x88613#32)]

def traceLds167_01 : List (List (BitVec 8)) :=
  [[0xc#8, 0xed#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8]]

theorem facts167_01 : ChainFacts (writeLog snapshotMem traceD167_01.log)
    (writeLog snapshotMem traceD167_01.log) traceD167_01.regs traceLds167_01 traceSeg167_01 := by
  have kind0 : (mkLine 0x8000eff8#64 0xfffff6b7#32).kind = MKind.lui := by decide
  have kind1 : (mkLine 0x8000effc#64 0xfff68693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000f000#64 0x2813083#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000f004#64 0xd7f7b3#32).kind = MKind.and := by decide
  have kind4 : (mkLine 0x8000f008#64 0x1271583#32).kind = MKind.lh := by decide
  have kind5 : (mkLine 0x8000f00c#64 0xf71823#32).kind = MKind.sh := by decide
  have kind6 : (mkLine 0x8000f010#64 0x30693#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000f014#64 0x88613#32).kind = MKind.addi := by decide
  simp only [traceSeg167_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00030693
    | exact DecodeTable.decode_00088613
    | exact DecodeTable.decode_00d7f7b3
    | exact DecodeTable.decode_00f71823
    | exact DecodeTable.decode_01271583
    | exact DecodeTable.decode_02813083
    | exact DecodeTable.decode_fff68693
    | exact DecodeTable.decode_fffff6b7
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run167_01 {c : Config} (h : TraceHolds traceD167_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD167_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg167_01 traceLds167_01 (by decide) facts167_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 202 ++ (evalBlocks traceSeg167_01 (SegEvalState.init traceD167_01.regs traceLds167_01)).log = traceStores.take 203
  have hw : (evalBlocks traceSeg167_01 (SegEvalState.init traceD167_01.regs traceLds167_01)).log = (traceStores.drop 202).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run167_01

#derive_case traceSeg167_02 chain
  [(0x8000f018#64, 0x80513#32),
   (0x8000f01c#64, 0x3010113#32)]
    terminator ⟨0x8000f020#64, 0x4dc0106f#32, 0x6f#8, 0x10#8, 0xc0#8, 0x4d#8, .j, 0, 0, 0#13, 0x0014dc#21, 0#12⟩

def traceLds167_02 : List (List (BitVec 8)) :=
  []

theorem facts167_02 : ChainFacts (writeLog snapshotMem traceD167_02.log)
    (writeLog snapshotMem traceD167_02.log) traceD167_02.regs traceLds167_02 traceSeg167_02 := by
  have kind0 : (mkLine 0x8000f018#64 0x80513#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f01c#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg167_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00080513
    | exact DecodeTable.decode_03010113
    | exact DecodeTable.decode_4dc0106f
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run167_02 {c : Config} (h : TraceHolds traceD167_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD167_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg167_02 traceLds167_02 (by decide) facts167_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 203 ++ (evalBlocks traceSeg167_02 (SegEvalState.init traceD167_02.regs traceLds167_02)).log = traceStores.take 203
  have hw : (evalBlocks traceSeg167_02 (SegEvalState.init traceD167_02.regs traceLds167_02)).log = (traceStores.drop 203).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run167_02

#derive_case traceSeg167_03 chain
  [(0x800104fc#64, 0x58793#32),
   (0x80010500#64, 0xff010113#32),
   (0x80010504#64, 0x813023#32),
   (0x80010508#64, 0x60593#32),
   (0x8001050c#64, 0x50413#32),
   (0x80010510#64, 0x68613#32),
   (0x80010514#64, 0x78513#32),
   (0x80010518#64, 0x113423#32)]

def traceLds167_03 : List (List (BitVec 8)) :=
  []

theorem facts167_03 : ChainFacts (writeLog snapshotMem traceD167_03.log)
    (writeLog snapshotMem traceD167_03.log) traceD167_03.regs traceLds167_03 traceSeg167_03 := by
  have kind0 : (mkLine 0x800104fc#64 0x58793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80010500#64 0xff010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80010504#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80010508#64 0x60593#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8001050c#64 0x50413#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80010510#64 0x68613#32).kind = MKind.addi := by decide
  have kind6 : (mkLine 0x80010514#64 0x78513#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80010518#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg167_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050413
    | exact DecodeTable.decode_00058793
    | exact DecodeTable.decode_00060593
    | exact DecodeTable.decode_00068613
    | exact DecodeTable.decode_00078513
    | exact DecodeTable.decode_00113423
    | exact DecodeTable.decode_00813023
    | exact DecodeTable.decode_ff010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run167_03 {c : Config} (h : TraceHolds traceD167_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD167_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg167_03 traceLds167_03 (by decide) facts167_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 203 ++ (evalBlocks traceSeg167_03 (SegEvalState.init traceD167_03.regs traceLds167_03)).log = traceStores.take 205
  have hw : (evalBlocks traceSeg167_03 (SegEvalState.init traceD167_03.regs traceLds167_03)).log = (traceStores.drop 203).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run167_03

#derive_case traceSeg167_04 chain
  [(0x8001051c#64, 0x4e01ac23#32)]

def traceLds167_04 : List (List (BitVec 8)) :=
  []

theorem facts167_04 : ChainFacts (writeLog snapshotMem traceD167_04.log)
    (writeLog snapshotMem traceD167_04.log) traceD167_04.regs traceLds167_04 traceSeg167_04 := by
  have kind0 : (mkLine 0x8001051c#64 0x4e01ac23#32).kind = MKind.sw := by decide
  simp only [traceSeg167_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_4e01ac23
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run167_04 {c : Config} (h : TraceHolds traceD167_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD168 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg167_04 traceLds167_04 (by decide) facts167_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 205 ++ (evalBlocks traceSeg167_04 (SegEvalState.init traceD167_04.regs traceLds167_04)).log = traceStores.take 206
  have hw : (evalBlocks traceSeg167_04 (SegEvalState.init traceD167_04.regs traceLds167_04)).log = (traceStores.drop 205).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run167_04
theorem run167 {c : Config} (h : TraceHolds traceD167 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD168 c' := by
  obtain ⟨c0, s0, h0⟩ := run167_00 h
  obtain ⟨c1, s1, h1⟩ := run167_01 h0
  obtain ⟨c2, s2, h2⟩ := run167_02 h1
  obtain ⟨c3, s3, h3⟩ := run167_03 h2
  obtain ⟨c4, s4, h4⟩ := run167_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run167
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts168 : TraceCallFacts traceD168 0xb1def0ef#32
    (instruction.JAL (0x1efb1c#21, gprIdx 1)) 0xef#8 0xf0#8 0xde#8 0xb1#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_b1def0ef

theorem run168 {c : Config} (h : TraceHolds traceD168 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD169 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb1def0ef#32 0x1efb1c#21 0xef#8 0xf0#8 0xde#8 0xb1#8 facts168 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run168
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg169 chain
  []
    terminator ⟨0x8000003c#64, 0x02060463#32, 0x63#8, 0x04#8, 0x06#8, 0x02#8, .br bop.BEQ false, 12, 0, 0x0028#13, 0#21, 0#12⟩ ;;
  [(0x80000040#64, 0x10100713#32),
   (0x80000044#64, 0xc586b3#32),
   (0x80000048#64, 0x3071713#32),
   (0x8000004c#64, 0x5c783#32),
   (0x80000050#64, 0x158593#32),
   (0x80000054#64, 0xe7e7b3#32),
   (0x80000058#64, 0x1b817#32)]

def traceLds169 : List (List (BitVec 8)) :=
  [[0xa#8]]

theorem facts169 : ChainFacts (writeLog snapshotMem traceD169.log)
    (writeLog snapshotMem traceD169.log) traceD169.regs traceLds169 traceSeg169 := by
  have kind0 : (mkLine 0x80000040#64 0x10100713#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80000044#64 0xc586b3#32).kind = MKind.add := by decide
  have kind2 : (mkLine 0x80000048#64 0x3071713#32).kind = MKind.slli := by decide
  have kind3 : (mkLine 0x8000004c#64 0x5c783#32).kind = MKind.lbu := by decide
  have kind4 : (mkLine 0x80000050#64 0x158593#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80000054#64 0xe7e7b3#32).kind = MKind.or := by decide
  have kind6 : (mkLine 0x80000058#64 0x1b817#32).kind = MKind.auipc := by decide
  simp only [traceSeg169, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0001b817
    | exact DecodeTable.decode_0005c783
    | exact DecodeTable.decode_00158593
    | exact DecodeTable.decode_00c586b3
    | exact DecodeTable.decode_00e7e7b3
    | exact DecodeTable.decode_02060463
    | exact DecodeTable.decode_03071713
    | exact DecodeTable.decode_10100713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run169 {c : Config} (h : TraceHolds traceD169 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD170 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg169 traceLds169 (by decide) facts169 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 206 ++ (evalBlocks traceSeg169 (SegEvalState.init traceD169.regs traceLds169)).log = traceStores.take 206
  have hw : (evalBlocks traceSeg169 (SegEvalState.init traceD169.regs traceLds169)).log = (traceStores.drop 206).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run169
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem run170 {c : Config} (h : TraceHolds traceD170 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD171 c' := by
  obtain ⟨c', hs, hp⟩ := h.putchar 0xa#8
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run170
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg171 chain
  []
    terminator ⟨0x80000060#64, 0xfed596e3#32, 0xe3#8, 0x96#8, 0xd5#8, 0xfe#8, .br bop.BNE false, 11, 13, 0x1fec#13, 0#21, 0#12⟩ ;;
  [(0x80000064#64, 0x60513#32)]
    terminator ⟨0x80000068#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds171 : List (List (BitVec 8)) :=
  []

theorem facts171 : ChainFacts (writeLog snapshotMem traceD171.log)
    (writeLog snapshotMem traceD171.log) traceD171.regs traceLds171 traceSeg171 := by
  have kind0 : (mkLine 0x80000064#64 0x60513#32).kind = MKind.addi := by decide
  simp only [traceSeg171, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00060513
    | exact DecodeTable.decode_fed596e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run171 {c : Config} (h : TraceHolds traceD171 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD172 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg171 traceLds171 (by decide) facts171 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 206 ++ (evalBlocks traceSeg171 (SegEvalState.init traceD171.regs traceLds171)).log = traceStores.take 206
  have hw : (evalBlocks traceSeg171 (SegEvalState.init traceD171.regs traceLds171)).log = (traceStores.drop 206).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run171
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg172 chain
  [(0x80010524#64, 0xfff00793#32)]
    terminator ⟨0x80010528#64, 0x00f50a63#32, 0x63#8, 0x0a#8, 0xf5#8, 0x00#8, .br bop.BEQ false, 10, 15, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8001052c#64, 0x813083#32),
   (0x80010530#64, 0x13403#32),
   (0x80010534#64, 0x1010113#32)]
    terminator ⟨0x80010538#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds172 : List (List (BitVec 8)) :=
  [[0xc#8, 0xed#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts172 : ChainFacts (writeLog snapshotMem traceD172.log)
    (writeLog snapshotMem traceD172.log) traceD172.regs traceLds172 traceSeg172 := by
  have kind0 : (mkLine 0x80010524#64 0xfff00793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8001052c#64 0x813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80010530#64 0x13403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80010534#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg172, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run172 {c : Config} (h : TraceHolds traceD172 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD173 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg172 traceLds172 (by decide) facts172 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 206 ++ (evalBlocks traceSeg172 (SegEvalState.init traceD172.regs traceLds172)).log = traceStores.take 206
  have hw : (evalBlocks traceSeg172 (SegEvalState.init traceD172.regs traceLds172)).log = (traceStores.drop 206).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run172
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg173 chain
  [(0x8000ed0c#64, 0x40a484bb#32)]
    terminator ⟨0x8000ed10#64, 0xfca04ee3#32, 0xe3#8, 0x4e#8, 0xa0#8, 0xfc#8, .br bop.BLT true, 0, 10, 0x1fdc#13, 0#21, 0#12⟩ ;;
  [(0x8000ecec#64, 0xa90933#32)]
    terminator ⟨0x8000ecf0#64, 0x04905e63#32, 0x63#8, 0x5e#8, 0x90#8, 0x04#8, .br bop.BGE true, 0, 9, 0x005c#13, 0#21, 0#12⟩ ;;
  [(0x8000ed4c#64, 0x1813483#32),
   (0x8000ed50#64, 0x1013903#32)]
    terminator ⟨0x8000ed54#64, 0xf49ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xf4#8, .j, 0, 0, 0#13, 0x1fff48#21, 0#12⟩ ;;
  [(0x8000ec9c#64, 0x2813083#32),
   (0x8000eca0#64, 0x2013403#32),
   (0x8000eca4#64, 0x813983#32),
   (0x8000eca8#64, 0x513#32),
   (0x8000ecac#64, 0x3010113#32)]
    terminator ⟨0x8000ecb0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds173 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xee#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts173 : ChainFacts (writeLog snapshotMem traceD173.log)
    (writeLog snapshotMem traceD173.log) traceD173.regs traceLds173 traceSeg173 := by
  have kind0 : (mkLine 0x8000ed0c#64 0x40a484bb#32).kind = MKind.subw := by decide
  have kind1 : (mkLine 0x8000ecec#64 0xa90933#32).kind = MKind.add := by decide
  have kind2 : (mkLine 0x8000ed4c#64 0x1813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ed50#64 0x1013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x8000ec9c#64 0x2813083#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000eca0#64 0x2013403#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x8000eca4#64 0x813983#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x8000eca8#64 0x513#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x8000ecac#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg173, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00813983
    | exact DecodeTable.decode_00a90933
    | exact DecodeTable.decode_01013903
    | exact DecodeTable.decode_01813483
    | exact DecodeTable.decode_02013403
    | exact DecodeTable.decode_02813083
    | exact DecodeTable.decode_03010113
    | exact DecodeTable.decode_04905e63
    | exact DecodeTable.decode_40a484bb
    | exact DecodeTable.decode_f49ff06f
    | exact DecodeTable.decode_fca04ee3
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run173 {c : Config} (h : TraceHolds traceD173 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD174 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg173 traceLds173 (by decide) facts173 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 206 ++ (evalBlocks traceSeg173 (SegEvalState.init traceD173.regs traceLds173)).log = traceStores.take 206
  have hw : (evalBlocks traceSeg173 (SegEvalState.init traceD173.regs traceLds173)).log = (traceStores.drop 206).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run173
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg174 chain
  [(0x8000ee10#64, 0x13583#32),
   (0x8000ee14#64, 0x50793#32),
   (0x8000ee18#64, 0xb05a703#32),
   (0x8000ee1c#64, 0x177713#32)]
    terminator ⟨0x8000ee20#64, 0x00071863#32, 0x63#8, 0x18#8, 0x07#8, 0x00#8, .br bop.BNE false, 14, 0, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000ee24#64, 0x105d703#32),
   (0x8000ee28#64, 0x20077713#32)]
    terminator ⟨0x8000ee2c#64, 0x02070863#32, 0x63#8, 0x08#8, 0x07#8, 0x02#8, .br bop.BEQ true, 14, 0, 0x0030#13, 0#21, 0#12⟩ ;;
  [(0x8000ee5c#64, 0xa13023#32),
   (0x8000ee60#64, 0xa05b503#32)]

def traceLds174 : List (List (BitVec 8)) :=
  [[0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts174 : ChainFacts (writeLog snapshotMem traceD174.log)
    (writeLog snapshotMem traceD174.log) traceD174.regs traceLds174 traceSeg174 := by
  have kind0 : (mkLine 0x8000ee10#64 0x13583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee14#64 0x50793#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ee18#64 0xb05a703#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000ee1c#64 0x177713#32).kind = MKind.andi := by decide
  have kind4 : (mkLine 0x8000ee24#64 0x105d703#32).kind = MKind.lhu := by decide
  have kind5 : (mkLine 0x8000ee28#64 0x20077713#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000ee5c#64 0xa13023#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x8000ee60#64 0xa05b503#32).kind = MKind.ld := by decide
  simp only [traceSeg174, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013583
    | exact DecodeTable.decode_00050793
    | exact DecodeTable.decode_00071863
    | exact DecodeTable.decode_00177713
    | exact DecodeTable.decode_00a13023
    | exact DecodeTable.decode_0105d703
    | exact DecodeTable.decode_02070863
    | exact DecodeTable.decode_0a05b503
    | exact DecodeTable.decode_0b05a703
    | exact DecodeTable.decode_20077713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run174 {c : Config} (h : TraceHolds traceD174 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD175 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg174 traceLds174 (by decide) facts174 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 206 ++ (evalBlocks traceSeg174 (SegEvalState.init traceD174.regs traceLds174)).log = traceStores.take 207
  have hw : (evalBlocks traceSeg174 (SegEvalState.init traceD174.regs traceLds174)).log = (traceStores.drop 206).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run174
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts175 : TraceCallFacts traceD175 0x994f80ef#32
    (instruction.JAL (0x1f8194#21, gprIdx 1)) 0xef#8 0x80#8 0x4f#8 0x99#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_994f80ef

theorem run175 {c : Config} (h : TraceHolds traceD175 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD176 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x994f80ef#32 0x1f8194#21 0xef#8 0x80#8 0x4f#8 0x99#8 facts175 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run175
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg176 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds176 : List (List (BitVec 8)) :=
  []

theorem facts176 : ChainFacts (writeLog snapshotMem traceD176.log)
    (writeLog snapshotMem traceD176.log) traceD176.regs traceLds176 traceSeg176 := by
  simp only [traceSeg176, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run176 {c : Config} (h : TraceHolds traceD176 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD177 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg176 traceLds176 (by decide) facts176 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 207 ++ (evalBlocks traceSeg176 (SegEvalState.init traceD176.regs traceLds176)).log = traceStores.take 207
  have hw : (evalBlocks traceSeg176 (SegEvalState.init traceD176.regs traceLds176)).log = (traceStores.drop 207).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run176
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg177 chain
  [(0x8000ee68#64, 0x13783#32),
   (0x8000ee6c#64, 0x1813083#32),
   (0x8000ee70#64, 0x78513#32),
   (0x8000ee74#64, 0x2010113#32)]
    terminator ⟨0x8000ee78#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds177 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xdc#8, 0xf1#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts177 : ChainFacts (writeLog snapshotMem traceD177.log)
    (writeLog snapshotMem traceD177.log) traceD177.regs traceLds177 traceSeg177 := by
  have kind0 : (mkLine 0x8000ee68#64 0x13783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee6c#64 0x1813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ee70#64 0x78513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ee74#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg177, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00013783
    | exact DecodeTable.decode_00078513
    | exact DecodeTable.decode_01813083
    | exact DecodeTable.decode_02010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run177 {c : Config} (h : TraceHolds traceD177 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD178 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg177 traceLds177 (by decide) facts177 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 207 ++ (evalBlocks traceSeg177 (SegEvalState.init traceD177.regs traceLds177)).log = traceStores.take 207
  have hw : (evalBlocks traceSeg177 (SegEvalState.init traceD177.regs traceLds177)).log = (traceStores.drop 207).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run177
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg178 chain
  []
    terminator ⟨0x8000f1dc#64, 0xf8050ae3#32, 0xe3#8, 0x0a#8, 0x05#8, 0xf8#8, .br bop.BEQ true, 10, 0, 0x1f94#13, 0#21, 0#12⟩ ;;
  [(0x8000f170#64, 0x2813083#32),
   (0x8000f174#64, 0x40513#32),
   (0x8000f178#64, 0x2013403#32),
   (0x8000f17c#64, 0x1813483#32),
   (0x8000f180#64, 0x3010113#32)]
    terminator ⟨0x8000f184#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds178 : List (List (BitVec 8)) :=
  [[0x40#8, 0xe7#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts178 : ChainFacts (writeLog snapshotMem traceD178.log)
    (writeLog snapshotMem traceD178.log) traceD178.regs traceLds178 traceSeg178 := by
  have kind0 : (mkLine 0x8000f170#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000f174#64 0x40513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000f178#64 0x2013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000f17c#64 0x1813483#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x8000f180#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg178, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00040513
    | exact DecodeTable.decode_01813483
    | exact DecodeTable.decode_02013403
    | exact DecodeTable.decode_02813083
    | exact DecodeTable.decode_03010113
    | exact DecodeTable.decode_f8050ae3
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run178 {c : Config} (h : TraceHolds traceD178 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD179 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg178 traceLds178 (by decide) facts178 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 207 ++ (evalBlocks traceSeg178 (SegEvalState.init traceD178.regs traceLds178)).log = traceStores.take 207
  have hw : (evalBlocks traceSeg178 (SegEvalState.init traceD178.regs traceLds178)).log = (traceStores.drop 207).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run178
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg179 chain
  [(0x8000e740#64, 0x813603#32),
   (0x8000e744#64, 0x50593#32)]
    terminator ⟨0x8000e748#64, 0xfc5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xfc#8, .j, 0, 0, 0#13, 0x1fffc4#21, 0#12⟩ ;;
  [(0x8000e70c#64, 0xb062783#32),
   (0x8000e710#64, 0x17f793#32)]
    terminator ⟨0x8000e714#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000e718#64, 0x1065783#32),
   (0x8000e71c#64, 0x2007f793#32)]
    terminator ⟨0x8000e720#64, 0x04078863#32, 0x63#8, 0x88#8, 0x07#8, 0x04#8, .br bop.BEQ true, 15, 0, 0x0050#13, 0#21, 0#12⟩ ;;
  [(0x8000e770#64, 0xa063503#32),
   (0x8000e774#64, 0xb13423#32)]

def traceLds179 : List (List (BitVec 8)) :=
  [[0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts179 : ChainFacts (writeLog snapshotMem traceD179.log)
    (writeLog snapshotMem traceD179.log) traceD179.regs traceLds179 traceSeg179 := by
  have kind0 : (mkLine 0x8000e740#64 0x813603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e744#64 0x50593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000e70c#64 0xb062783#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000e710#64 0x17f793#32).kind = MKind.andi := by decide
  have kind4 : (mkLine 0x8000e718#64 0x1065783#32).kind = MKind.lhu := by decide
  have kind5 : (mkLine 0x8000e71c#64 0x2007f793#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000e770#64 0xa063503#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x8000e774#64 0xb13423#32).kind = MKind.sd := by decide
  simp only [traceSeg179, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050593
    | exact DecodeTable.decode_00079863
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_00813603
    | exact DecodeTable.decode_00b13423
    | exact DecodeTable.decode_01065783
    | exact DecodeTable.decode_04078863
    | exact DecodeTable.decode_0a063503
    | exact DecodeTable.decode_0b062783
    | exact DecodeTable.decode_2007f793
    | exact DecodeTable.decode_fc5ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run179 {c : Config} (h : TraceHolds traceD179 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD180 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg179 traceLds179 (by decide) facts179 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 207 ++ (evalBlocks traceSeg179 (SegEvalState.init traceD179.regs traceLds179)).log = traceStores.take 208
  have hw : (evalBlocks traceSeg179 (SegEvalState.init traceD179.regs traceLds179)).log = (traceStores.drop 207).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run179
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts180 : TraceCallFacts traceD180 0x881f80ef#32
    (instruction.JAL (0x1f8880#21, gprIdx 1)) 0xef#8 0x80#8 0x1f#8 0x88#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_881f80ef

theorem run180 {c : Config} (h : TraceHolds traceD180 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD181 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x881f80ef#32 0x1f8880#21 0xef#8 0x80#8 0x1f#8 0x88#8 facts180 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run180
end Vsa.Sim.OutputAliasLoaded
