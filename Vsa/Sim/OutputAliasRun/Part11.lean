import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part30
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part13
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part25
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part15
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch14Part26
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts221 : TraceCallFacts traceD221 0xc9cf80ef#32
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

theorem run221 {c : Config} (h : TraceHolds traceD221 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD222 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc9cf80ef#32 0x1f849c#21 0xef#8 0x80#8 0xcf#8 0xc9#8 facts221 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run221
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg222 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds222 : List (List (BitVec 8)) :=
  []

theorem facts222 : ChainFacts (writeLog snapshotMem traceD222.log)
    (writeLog snapshotMem traceD222.log) traceD222.regs traceLds222 traceSeg222 := by
  simp only [traceSeg222, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run222 {c : Config} (h : TraceHolds traceD222 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD223 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg222 traceLds222 (by decide) facts222 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg222 (SegEvalState.init traceD222.regs traceLds222)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg222 (SegEvalState.init traceD222.regs traceLds222)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run222
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg223 chain
  []
    terminator ⟨0x8000eb60#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0#13, 0x1fff54#21, 0#12⟩ ;;
  [(0x8000eab4#64, 0xa043503#32)]

def traceLds223 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts223 : ChainFacts (writeLog snapshotMem traceD223.log)
    (writeLog snapshotMem traceD223.log) traceD223.regs traceLds223 traceSeg223 := by
  have kind0 : (mkLine 0x8000eab4#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg223, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | exact DecodeTable.decode_f55ff06f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run223 {c : Config} (h : TraceHolds traceD223 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD224 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg223 traceLds223 (by decide) facts223 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg223 (SegEvalState.init traceD223.regs traceLds223)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg223 (SegEvalState.init traceD223.regs traceLds223)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run223
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts224 : TraceCallFacts traceD224 0xd20f80ef#32
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

theorem run224 {c : Config} (h : TraceHolds traceD224 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD225 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xd20f80ef#32 0x1f8520#21 0xef#8 0x80#8 0xf#8 0xd2#8 facts224 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run224
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg225 chain
  []
    terminator ⟨0x80006fd8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds225 : List (List (BitVec 8)) :=
  []

theorem facts225 : ChainFacts (writeLog snapshotMem traceD225.log)
    (writeLog snapshotMem traceD225.log) traceD225.regs traceLds225 traceSeg225 := by
  simp only [traceSeg225, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run225 {c : Config} (h : TraceHolds traceD225 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD226 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg225 traceLds225 (by decide) facts225 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg225 (SegEvalState.init traceD225.regs traceLds225)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg225 (SegEvalState.init traceD225.regs traceLds225)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run225
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts226 : TraceCallFacts traceD226 0xe6cf70ef#32
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

theorem run226 {c : Config} (h : TraceHolds traceD226 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD227 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe6cf70ef#32 0x1f766c#21 0xef#8 0x70#8 0xcf#8 0xe6#8 facts226 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run226
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg227 chain
  [(0x80006128#64, 0x4e018513#32)]
    terminator ⟨0x8000612c#64, 0x6cd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6c#8, .j, 0, 0, 0#13, 0x000ecc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds227 : List (List (BitVec 8)) :=
  []

theorem facts227 : ChainFacts (writeLog snapshotMem traceD227.log)
    (writeLog snapshotMem traceD227.log) traceD227.regs traceLds227 traceSeg227 := by
  have kind0 : (mkLine 0x80006128#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg227, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6cd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run227 {c : Config} (h : TraceHolds traceD227 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD228 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg227 traceLds227 (by decide) facts227 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg227 (SegEvalState.init traceD227.regs traceLds227)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg227 (SegEvalState.init traceD227.regs traceLds227)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run227
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg228 chain
  [(0x8000eac0#64, 0x1813083#32),
   (0x8000eac4#64, 0x1013403#32),
   (0x8000eac8#64, 0x813483#32),
   (0x8000eacc#64, 0x90513#32),
   (0x8000ead0#64, 0x13903#32),
   (0x8000ead4#64, 0x2010113#32)]
    terminator ⟨0x8000ead8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds228 : List (List (BitVec 8)) :=
  [[0xf0#8, 0xe3#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x68#8, 0xba#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x90#8, 0xbc#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts228 : ChainFacts (writeLog snapshotMem traceD228.log)
    (writeLog snapshotMem traceD228.log) traceD228.regs traceLds228 traceSeg228 := by
  have kind0 : (mkLine 0x8000eac0#64 0x1813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eac4#64 0x1013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eac8#64 0x813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eacc#64 0x90513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000ead0#64 0x13903#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000ead4#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg228, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run228 {c : Config} (h : TraceHolds traceD228 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD229 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg228 traceLds228 (by decide) facts228 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg228 (SegEvalState.init traceD228.regs traceLds228)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg228 (SegEvalState.init traceD228.regs traceLds228)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run228
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD229_01 : TraceData :=
  { pc := 0x8000e3d4#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 240,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD229_02 : TraceData :=
  { pc := 0x8000e3dc#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x200a#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 240,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg229_00 chain
  [(0x8000e3f0#64, 0x1656b33#32),
   (0x8000e3f4#64, 0xb0b1b#32),
   (0x8000e3f8#64, 0xb840413#32)]
    terminator ⟨0x8000e3fc#64, 0xfc941ce3#32, 0xe3#8, 0x1c#8, 0x94#8, 0xfc#8, .br bop.BNE true, 8, 9, 0x1fd8#13, 0#21, 0#12⟩

def traceLds229_00 : List (List (BitVec 8)) :=
  []

theorem facts229_00 : ChainFacts (writeLog snapshotMem traceD229.log)
    (writeLog snapshotMem traceD229.log) traceD229.regs traceLds229_00 traceSeg229_00 := by
  have kind0 : (mkLine 0x8000e3f0#64 0x1656b33#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x8000e3f4#64 0xb0b1b#32).kind = MKind.addiw := by decide
  have kind2 : (mkLine 0x8000e3f8#64 0xb840413#32).kind = MKind.addi := by decide
  simp only [traceSeg229_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run229_00 {c : Config} (h : TraceHolds traceD229 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD229_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg229_00 traceLds229_00 (by decide) facts229_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg229_00 (SegEvalState.init traceD229.regs traceLds229_00)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg229_00 (SegEvalState.init traceD229.regs traceLds229_00)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run229_00

#derive_case traceSeg229_01 chain
  [(0x8000e3d4#64, 0x1045783#32)]
    terminator ⟨0x8000e3d8#64, 0x02fbf063#32, 0x63#8, 0xf0#8, 0xfb#8, 0x02#8, .br bop.BGEU false, 23, 15, 0x0020#13, 0#21, 0#12⟩

def traceLds229_01 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts229_01 : ChainFacts (writeLog snapshotMem traceD229_01.log)
    (writeLog snapshotMem traceD229_01.log) traceD229_01.regs traceLds229_01 traceSeg229_01 := by
  have kind0 : (mkLine 0x8000e3d4#64 0x1045783#32).kind = MKind.lhu := by decide
  simp only [traceSeg229_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_02fbf063
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run229_01 {c : Config} (h : TraceHolds traceD229_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD229_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg229_01 traceLds229_01 (by decide) facts229_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg229_01 (SegEvalState.init traceD229_01.regs traceLds229_01)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg229_01 (SegEvalState.init traceD229_01.regs traceLds229_01)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run229_01

#derive_case traceSeg229_02 chain
  [(0x8000e3dc#64, 0x1241783#32),
   (0x8000e3e0#64, 0x40593#32),
   (0x8000e3e4#64, 0xa0513#32)]
    terminator ⟨0x8000e3e8#64, 0x01378863#32, 0x63#8, 0x88#8, 0x37#8, 0x01#8, .br bop.BEQ false, 15, 19, 0x0010#13, 0#21, 0#12⟩

def traceLds229_02 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8]]

theorem facts229_02 : ChainFacts (writeLog snapshotMem traceD229_02.log)
    (writeLog snapshotMem traceD229_02.log) traceD229_02.regs traceLds229_02 traceSeg229_02 := by
  have kind0 : (mkLine 0x8000e3dc#64 0x1241783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000e3e0#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000e3e4#64 0xa0513#32).kind = MKind.addi := by decide
  simp only [traceSeg229_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run229_02 {c : Config} (h : TraceHolds traceD229_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD230 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg229_02 traceLds229_02 (by decide) facts229_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg229_02 (SegEvalState.init traceD229_02.regs traceLds229_02)).log = traceStores.take 240
  have hw : (evalBlocks traceSeg229_02 (SegEvalState.init traceD229_02.regs traceLds229_02)).log = (traceStores.drop 240).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run229_02
theorem run229 {c : Config} (h : TraceHolds traceD229 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD230 c' := by
  obtain ⟨c0, s0, h0⟩ := run229_00 h
  obtain ⟨c1, s1, h1⟩ := run229_01 h0
  obtain ⟨c2, s2, h2⟩ := run229_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run229
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts230 : TraceCallFacts traceD230 0xa80e7#32
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

theorem run230 {c : Config} (h : TraceHolds traceD230 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0xa80e7#32 0x0#12 21 0x8000e9f8#64
    0xe7#8 0x80#8 0xa#8 0x0#8 facts230
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run230
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD231_01 : TraceData :=
  { pc := 0x8000ea08#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001bc90#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x1#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 242,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD231_02 : TraceData :=
  { pc := 0x8000ea1c#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x1#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 244,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD231_03 : TraceData :=
  { pc := 0x8000ea24#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x4#64), (15, 0x80005d2c#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 244,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD231_04 : TraceData :=
  { pc := 0x8000ea34#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 244,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD231_05 : TraceData :=
  { pc := 0x8000eb28#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 244,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg231_00 chain
  [(0x8000e9f8#64, 0xfe010113#32),
   (0x8000e9fc#64, 0x113c23#32),
   (0x8000ea00#64, 0x1213023#32)]
    terminator ⟨0x8000ea04#64, 0x0e058263#32, 0x63#8, 0x82#8, 0x05#8, 0x0e#8, .br bop.BEQ false, 11, 0, 0x00e4#13, 0#21, 0#12⟩

def traceLds231_00 : List (List (BitVec 8)) :=
  []

theorem facts231_00 : ChainFacts (writeLog snapshotMem traceD231.log)
    (writeLog snapshotMem traceD231.log) traceD231.regs traceLds231_00 traceSeg231_00 := by
  have kind0 : (mkLine 0x8000e9f8#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e9fc#64 0x113c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea00#64 0x1213023#32).kind = MKind.sd := by decide
  simp only [traceSeg231_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run231_00 {c : Config} (h : TraceHolds traceD231 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_00 traceLds231_00 (by decide) facts231_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 240 ++ (evalBlocks traceSeg231_00 (SegEvalState.init traceD231.regs traceLds231_00)).log = traceStores.take 242
  have hw : (evalBlocks traceSeg231_00 (SegEvalState.init traceD231.regs traceLds231_00)).log = (traceStores.drop 240).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_00

#derive_case traceSeg231_01 chain
  [(0x8000ea08#64, 0x813823#32),
   (0x8000ea0c#64, 0x913423#32),
   (0x8000ea10#64, 0x58413#32),
   (0x8000ea14#64, 0x50493#32)]
    terminator ⟨0x8000ea18#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds231_01 : List (List (BitVec 8)) :=
  []

theorem facts231_01 : ChainFacts (writeLog snapshotMem traceD231_01.log)
    (writeLog snapshotMem traceD231_01.log) traceD231_01.regs traceLds231_01 traceSeg231_01 := by
  have kind0 : (mkLine 0x8000ea08#64 0x813823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ea0c#64 0x913423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea10#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ea14#64 0x50493#32).kind = MKind.addi := by decide
  simp only [traceSeg231_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run231_01 {c : Config} (h : TraceHolds traceD231_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_01 traceLds231_01 (by decide) facts231_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 242 ++ (evalBlocks traceSeg231_01 (SegEvalState.init traceD231_01.regs traceLds231_01)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg231_01 (SegEvalState.init traceD231_01.regs traceLds231_01)).log = (traceStores.drop 242).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_01

#derive_case traceSeg231_02 chain
  [(0x8000ea1c#64, 0x4853783#32)]
    terminator ⟨0x8000ea20#64, 0x10078063#32, 0x63#8, 0x80#8, 0x07#8, 0x10#8, .br bop.BEQ false, 15, 0, 0x0100#13, 0#21, 0#12⟩

def traceLds231_02 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts231_02 : ChainFacts (writeLog snapshotMem traceD231_02.log)
    (writeLog snapshotMem traceD231_02.log) traceD231_02.regs traceLds231_02 traceSeg231_02 := by
  have kind0 : (mkLine 0x8000ea1c#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg231_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact OutputAliasDecode.decode_10078063
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run231_02 {c : Config} (h : TraceHolds traceD231_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_02 traceLds231_02 (by decide) facts231_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg231_02 (SegEvalState.init traceD231_02.regs traceLds231_02)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg231_02 (SegEvalState.init traceD231_02.regs traceLds231_02)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_02

#derive_case traceSeg231_03 chain
  [(0x8000ea24#64, 0xb042783#32),
   (0x8000ea28#64, 0x1041703#32),
   (0x8000ea2c#64, 0x17f793#32)]
    terminator ⟨0x8000ea30#64, 0x0a079663#32, 0x63#8, 0x96#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00ac#13, 0#21, 0#12⟩

def traceLds231_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8]]

theorem facts231_03 : ChainFacts (writeLog snapshotMem traceD231_03.log)
    (writeLog snapshotMem traceD231_03.log) traceD231_03.regs traceLds231_03 traceSeg231_03 := by
  have kind0 : (mkLine 0x8000ea24#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000ea28#64 0x1041703#32).kind = MKind.lh := by decide
  have kind2 : (mkLine 0x8000ea2c#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg231_03, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run231_03 {c : Config} (h : TraceHolds traceD231_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_03 traceLds231_03 (by decide) facts231_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg231_03 (SegEvalState.init traceD231_03.regs traceLds231_03)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg231_03 (SegEvalState.init traceD231_03.regs traceLds231_03)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_03

#derive_case traceSeg231_04 chain
  [(0x8000ea34#64, 0x20077713#32)]
    terminator ⟨0x8000ea38#64, 0x0e070863#32, 0x63#8, 0x08#8, 0x07#8, 0x0e#8, .br bop.BEQ true, 14, 0, 0x00f0#13, 0#21, 0#12⟩

def traceLds231_04 : List (List (BitVec 8)) :=
  []

theorem facts231_04 : ChainFacts (writeLog snapshotMem traceD231_04.log)
    (writeLog snapshotMem traceD231_04.log) traceD231_04.regs traceLds231_04 traceSeg231_04 := by
  have kind0 : (mkLine 0x8000ea34#64 0x20077713#32).kind = MKind.andi := by decide
  simp only [traceSeg231_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_20077713
    | exact OutputAliasDecode.decode_0e070863
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run231_04 {c : Config} (h : TraceHolds traceD231_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD231_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_04 traceLds231_04 (by decide) facts231_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg231_04 (SegEvalState.init traceD231_04.regs traceLds231_04)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg231_04 (SegEvalState.init traceD231_04.regs traceLds231_04)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_04

#derive_case traceSeg231_05 chain
  [(0x8000eb28#64, 0xa043503#32)]

def traceLds231_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts231_05 : ChainFacts (writeLog snapshotMem traceD231_05.log)
    (writeLog snapshotMem traceD231_05.log) traceD231_05.regs traceLds231_05 traceSeg231_05 := by
  have kind0 : (mkLine 0x8000eb28#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg231_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run231_05 {c : Config} (h : TraceHolds traceD231_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD232 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg231_05 traceLds231_05 (by decide) facts231_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg231_05 (SegEvalState.init traceD231_05.regs traceLds231_05)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg231_05 (SegEvalState.init traceD231_05.regs traceLds231_05)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run231_05
theorem run231 {c : Config} (h : TraceHolds traceD231 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD232 c' := by
  obtain ⟨c0, s0, h0⟩ := run231_00 h
  obtain ⟨c1, s1, h1⟩ := run231_01 h0
  obtain ⟨c2, s2, h2⟩ := run231_02 h1
  obtain ⟨c3, s3, h3⟩ := run231_03 h2
  obtain ⟨c4, s4, h4⟩ := run231_04 h3
  obtain ⟨c5, s5, h5⟩ := run231_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run231
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts232 : TraceCallFacts traceD232 0xcb4f80ef#32
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

theorem run232 {c : Config} (h : TraceHolds traceD232 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD233 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xcb4f80ef#32 0x1f84b4#21 0xef#8 0x80#8 0x4f#8 0xcb#8 facts232 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run232
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg233 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds233 : List (List (BitVec 8)) :=
  []

theorem facts233 : ChainFacts (writeLog snapshotMem traceD233.log)
    (writeLog snapshotMem traceD233.log) traceD233.regs traceLds233 traceSeg233 := by
  simp only [traceSeg233, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run233 {c : Config} (h : TraceHolds traceD233 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD234 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg233 traceLds233 (by decide) facts233 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg233 (SegEvalState.init traceD233.regs traceLds233)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg233 (SegEvalState.init traceD233.regs traceLds233)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run233
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg234 chain
  [(0x8000eb30#64, 0x1041783#32)]
    terminator ⟨0x8000eb34#64, 0xf00794e3#32, 0xe3#8, 0x94#8, 0x07#8, 0xf0#8, .br bop.BNE true, 15, 0, 0x1f08#13, 0#21, 0#12⟩ ;;
  [(0x8000ea3c#64, 0x40593#32),
   (0x8000ea40#64, 0x48513#32)]

def traceLds234 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts234 : ChainFacts (writeLog snapshotMem traceD234.log)
    (writeLog snapshotMem traceD234.log) traceD234.regs traceLds234 traceSeg234 := by
  have kind0 : (mkLine 0x8000eb30#64 0x1041783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000ea3c#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea40#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg234, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run234 {c : Config} (h : TraceHolds traceD234 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD235 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg234 traceLds234 (by decide) facts234 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg234 (SegEvalState.init traceD234.regs traceLds234)).log = traceStores.take 244
  have hw : (evalBlocks traceSeg234 (SegEvalState.init traceD234.regs traceLds234)).log = (traceStores.drop 244).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run234
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts235 : TraceCallFacts traceD235 0x12c000ef#32
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

theorem run235 {c : Config} (h : TraceHolds traceD235 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x12c000ef#32 0x12c#21 0xef#8 0x0#8 0xc0#8 0x12#8 facts235 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run235
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD236_01 : TraceData :=
  { pc := 0x8000eb80#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x200a#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 246,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_02 : TraceData :=
  { pc := 0x8000ecb4#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 247,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_03 : TraceData :=
  { pc := 0x8000ecc0#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 248,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_04 : TraceData :=
  { pc := 0x8000ecd0#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001bb97#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x8#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 250,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_05 : TraceData :=
  { pc := 0x8000ece0#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 250,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_06 : TraceData :=
  { pc := 0x8000ece8#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 251,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_07 : TraceData :=
  { pc := 0x8000ed4c#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x0#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 251,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_08 : TraceData :=
  { pc := 0x8000ec9c#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0x8001b538#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 251,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD236_09 : TraceData :=
  { pc := 0x8000ecac#64,
    regs := [(1, 0x8000ea48#64), (2, 0x87ffff50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x0#64), (11, 0x8001bb20#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 251,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg236_00 chain
  [(0x8000eb70#64, 0x1059703#32),
   (0x8000eb74#64, 0xfd010113#32),
   (0x8000eb78#64, 0x2813023#32),
   (0x8000eb7c#64, 0x1313423#32)]

def traceLds236_00 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts236_00 : ChainFacts (writeLog snapshotMem traceD236.log)
    (writeLog snapshotMem traceD236.log) traceD236.regs traceLds236_00 traceSeg236_00 := by
  have kind0 : (mkLine 0x8000eb70#64 0x1059703#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000eb74#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb78#64 0x2813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000eb7c#64 0x1313423#32).kind = MKind.sd := by decide
  simp only [traceSeg236_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run236_00 {c : Config} (h : TraceHolds traceD236 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_00 traceLds236_00 (by decide) facts236_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 244 ++ (evalBlocks traceSeg236_00 (SegEvalState.init traceD236.regs traceLds236_00)).log = traceStores.take 246
  have hw : (evalBlocks traceSeg236_00 (SegEvalState.init traceD236.regs traceLds236_00)).log = (traceStores.drop 244).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_00

#derive_case traceSeg236_01 chain
  [(0x8000eb80#64, 0x2113423#32),
   (0x8000eb84#64, 0x877793#32),
   (0x8000eb88#64, 0x58413#32),
   (0x8000eb8c#64, 0x50993#32)]
    terminator ⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE true, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds236_01 : List (List (BitVec 8)) :=
  []

theorem facts236_01 : ChainFacts (writeLog snapshotMem traceD236_01.log)
    (writeLog snapshotMem traceD236_01.log) traceD236_01.regs traceLds236_01 traceSeg236_01 := by
  have kind0 : (mkLine 0x8000eb80#64 0x2113423#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000eb84#64 0x877793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000eb88#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000eb8c#64 0x50993#32).kind = MKind.addi := by decide
  simp only [traceSeg236_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run236_01 {c : Config} (h : TraceHolds traceD236_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_01 traceLds236_01 (by decide) facts236_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 246 ++ (evalBlocks traceSeg236_01 (SegEvalState.init traceD236_01.regs traceLds236_01)).log = traceStores.take 247
  have hw : (evalBlocks traceSeg236_01 (SegEvalState.init traceD236_01.regs traceLds236_01)).log = (traceStores.drop 246).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_01

#derive_case traceSeg236_02 chain
  [(0x8000ecb4#64, 0x1213823#32),
   (0x8000ecb8#64, 0x185b903#32)]
    terminator ⟨0x8000ecbc#64, 0x08090a63#32, 0x63#8, 0x0a#8, 0x09#8, 0x08#8, .br bop.BEQ false, 18, 0, 0x0094#13, 0#21, 0#12⟩

def traceLds236_02 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts236_02 : ChainFacts (writeLog snapshotMem traceD236_02.log)
    (writeLog snapshotMem traceD236_02.log) traceD236_02.regs traceLds236_02 traceSeg236_02 := by
  have kind0 : (mkLine 0x8000ecb4#64 0x1213823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecb8#64 0x185b903#32).kind = MKind.ld := by decide
  simp only [traceSeg236_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01213823
    | exact DecodeTable.decode_0185b903
    | exact DecodeTable.decode_08090a63
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_02 {c : Config} (h : TraceHolds traceD236_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_02 traceLds236_02 (by decide) facts236_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 247 ++ (evalBlocks traceSeg236_02 (SegEvalState.init traceD236_02.regs traceLds236_02)).log = traceStores.take 248
  have hw : (evalBlocks traceSeg236_02 (SegEvalState.init traceD236_02.regs traceLds236_02)).log = (traceStores.drop 247).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_02

#derive_case traceSeg236_03 chain
  [(0x8000ecc0#64, 0x913c23#32),
   (0x8000ecc4#64, 0x5b483#32),
   (0x8000ecc8#64, 0x377713#32),
   (0x8000eccc#64, 0x125b023#32)]

def traceLds236_03 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts236_03 : ChainFacts (writeLog snapshotMem traceD236_03.log)
    (writeLog snapshotMem traceD236_03.log) traceD236_03.regs traceLds236_03 traceSeg236_03 := by
  have kind0 : (mkLine 0x8000ecc0#64 0x913c23#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecc4#64 0x5b483#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ecc8#64 0x377713#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eccc#64 0x125b023#32).kind = MKind.sd := by decide
  simp only [traceSeg236_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0005b483
    | exact DecodeTable.decode_00377713
    | exact DecodeTable.decode_00913c23
    | exact DecodeTable.decode_0125b023
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_03 {c : Config} (h : TraceHolds traceD236_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_03 traceLds236_03 (by decide) facts236_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 248 ++ (evalBlocks traceSeg236_03 (SegEvalState.init traceD236_03.regs traceLds236_03)).log = traceStores.take 250
  have hw : (evalBlocks traceSeg236_03 (SegEvalState.init traceD236_03.regs traceLds236_03)).log = (traceStores.drop 248).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_03

#derive_case traceSeg236_04 chain
  [(0x8000ecd0#64, 0x412484bb#32),
   (0x8000ecd4#64, 0x793#32)]
    terminator ⟨0x8000ecd8#64, 0x00071463#32, 0x63#8, 0x14#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x0008#13, 0#21, 0#12⟩

def traceLds236_04 : List (List (BitVec 8)) :=
  []

theorem facts236_04 : ChainFacts (writeLog snapshotMem traceD236_04.log)
    (writeLog snapshotMem traceD236_04.log) traceD236_04.regs traceLds236_04 traceSeg236_04 := by
  have kind0 : (mkLine 0x8000ecd0#64 0x412484bb#32).kind = MKind.subw := by decide
  have kind1 : (mkLine 0x8000ecd4#64 0x793#32).kind = MKind.addi := by decide
  simp only [traceSeg236_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000793
    | exact DecodeTable.decode_00071463
    | exact DecodeTable.decode_412484bb
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_04 {c : Config} (h : TraceHolds traceD236_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_04 traceLds236_04 (by decide) facts236_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 250 ++ (evalBlocks traceSeg236_04 (SegEvalState.init traceD236_04.regs traceLds236_04)).log = traceStores.take 250
  have hw : (evalBlocks traceSeg236_04 (SegEvalState.init traceD236_04.regs traceLds236_04)).log = (traceStores.drop 250).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_04

#derive_case traceSeg236_05 chain
  [(0x8000ece0#64, 0xf42623#32)]
    terminator ⟨0x8000ece4#64, 0x00904863#32, 0x63#8, 0x48#8, 0x90#8, 0x00#8, .br bop.BLT false, 0, 9, 0x0010#13, 0#21, 0#12⟩

def traceLds236_05 : List (List (BitVec 8)) :=
  []

theorem facts236_05 : ChainFacts (writeLog snapshotMem traceD236_05.log)
    (writeLog snapshotMem traceD236_05.log) traceD236_05.regs traceLds236_05 traceSeg236_05 := by
  have kind0 : (mkLine 0x8000ece0#64 0xf42623#32).kind = MKind.sw := by decide
  simp only [traceSeg236_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00904863
    | exact DecodeTable.decode_00f42623
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_05 {c : Config} (h : TraceHolds traceD236_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_05 traceLds236_05 (by decide) facts236_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 250 ++ (evalBlocks traceSeg236_05 (SegEvalState.init traceD236_05.regs traceLds236_05)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg236_05 (SegEvalState.init traceD236_05.regs traceLds236_05)).log = (traceStores.drop 250).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_05

#derive_case traceSeg236_06 chain
  []
    terminator ⟨0x8000ece8#64, 0x0640006f#32, 0x6f#8, 0x00#8, 0x40#8, 0x06#8, .j, 0, 0, 0#13, 0x000064#21, 0#12⟩

def traceLds236_06 : List (List (BitVec 8)) :=
  []

theorem facts236_06 : ChainFacts (writeLog snapshotMem traceD236_06.log)
    (writeLog snapshotMem traceD236_06.log) traceD236_06.regs traceLds236_06 traceSeg236_06 := by
  simp only [traceSeg236_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0640006f
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_06 {c : Config} (h : TraceHolds traceD236_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_06 traceLds236_06 (by decide) facts236_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg236_06 (SegEvalState.init traceD236_06.regs traceLds236_06)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg236_06 (SegEvalState.init traceD236_06.regs traceLds236_06)).log = (traceStores.drop 251).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_06

#derive_case traceSeg236_07 chain
  [(0x8000ed4c#64, 0x1813483#32),
   (0x8000ed50#64, 0x1013903#32)]
    terminator ⟨0x8000ed54#64, 0xf49ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xf4#8, .j, 0, 0, 0#13, 0x1fff48#21, 0#12⟩

def traceLds236_07 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts236_07 : ChainFacts (writeLog snapshotMem traceD236_07.log)
    (writeLog snapshotMem traceD236_07.log) traceD236_07.regs traceLds236_07 traceSeg236_07 := by
  have kind0 : (mkLine 0x8000ed4c#64 0x1813483#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ed50#64 0x1013903#32).kind = MKind.ld := by decide
  simp only [traceSeg236_07, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01013903
    | exact DecodeTable.decode_01813483
    | exact DecodeTable.decode_f49ff06f
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_07 {c : Config} (h : TraceHolds traceD236_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_08 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_07 traceLds236_07 (by decide) facts236_07 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg236_07 (SegEvalState.init traceD236_07.regs traceLds236_07)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg236_07 (SegEvalState.init traceD236_07.regs traceLds236_07)).log = (traceStores.drop 251).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_07

#derive_case traceSeg236_08 chain
  [(0x8000ec9c#64, 0x2813083#32),
   (0x8000eca0#64, 0x2013403#32),
   (0x8000eca4#64, 0x813983#32),
   (0x8000eca8#64, 0x513#32)]

def traceLds236_08 : List (List (BitVec 8)) :=
  [[0x48#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8, 0xff#8]]

theorem facts236_08 : ChainFacts (writeLog snapshotMem traceD236_08.log)
    (writeLog snapshotMem traceD236_08.log) traceD236_08.regs traceLds236_08 traceSeg236_08 := by
  have kind0 : (mkLine 0x8000ec9c#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eca0#64 0x2013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eca4#64 0x813983#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eca8#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg236_08, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run236_08 {c : Config} (h : TraceHolds traceD236_08 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD236_09 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_08 traceLds236_08 (by decide) facts236_08 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg236_08 (SegEvalState.init traceD236_08.regs traceLds236_08)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg236_08 (SegEvalState.init traceD236_08.regs traceLds236_08)).log = (traceStores.drop 251).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_08

#derive_case traceSeg236_09 chain
  [(0x8000ecac#64, 0x3010113#32)]
    terminator ⟨0x8000ecb0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds236_09 : List (List (BitVec 8)) :=
  []

theorem facts236_09 : ChainFacts (writeLog snapshotMem traceD236_09.log)
    (writeLog snapshotMem traceD236_09.log) traceD236_09.regs traceLds236_09 traceSeg236_09 := by
  have kind0 : (mkLine 0x8000ecac#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg236_09, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_03010113
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run236_09 {c : Config} (h : TraceHolds traceD236_09 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD237 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg236_09 traceLds236_09 (by decide) facts236_09 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg236_09 (SegEvalState.init traceD236_09.regs traceLds236_09)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg236_09 (SegEvalState.init traceD236_09.regs traceLds236_09)).log = (traceStores.drop 251).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run236_09
theorem run236 {c : Config} (h : TraceHolds traceD236 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD237 c' := by
  obtain ⟨c0, s0, h0⟩ := run236_00 h
  obtain ⟨c1, s1, h1⟩ := run236_01 h0
  obtain ⟨c2, s2, h2⟩ := run236_02 h1
  obtain ⟨c3, s3, h3⟩ := run236_03 h2
  obtain ⟨c4, s4, h4⟩ := run236_04 h3
  obtain ⟨c5, s5, h5⟩ := run236_05 h4
  obtain ⟨c6, s6, h6⟩ := run236_06 h5
  obtain ⟨c7, s7, h7⟩ := run236_07 h6
  obtain ⟨c8, s8, h8⟩ := run236_08 h7
  obtain ⟨c9, s9, h9⟩ := run236_09 h8
  exact ⟨c9, (((((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9, h9⟩

#print axioms run236
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg237 chain
  [(0x8000ea48#64, 0x5043783#32),
   (0x8000ea4c#64, 0x50913#32)]
    terminator ⟨0x8000ea50#64, 0x00078a63#32, 0x63#8, 0x8a#8, 0x07#8, 0x00#8, .br bop.BEQ false, 15, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8000ea54#64, 0x3043583#32),
   (0x8000ea58#64, 0x48513#32)]

def traceLds237 : List (List (BitVec 8)) :=
  [[0xc0#8, 0xf0#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts237 : ChainFacts (writeLog snapshotMem traceD237.log)
    (writeLog snapshotMem traceD237.log) traceD237.regs traceLds237 traceSeg237 := by
  have kind0 : (mkLine 0x8000ea48#64 0x5043783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ea4c#64 0x50913#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea54#64 0x3043583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea58#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg237, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run237 {c : Config} (h : TraceHolds traceD237 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD238 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg237 traceLds237 (by decide) facts237 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg237 (SegEvalState.init traceD237.regs traceLds237)).log = traceStores.take 251
  have hw : (evalBlocks traceSeg237 (SegEvalState.init traceD237.regs traceLds237)).log = (traceStores.drop 251).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run237
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts238 : TraceCallFacts traceD238 0x780e7#32
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

theorem run238 {c : Config} (h : TraceHolds traceD238 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD239 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x8000f0c0#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts238
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run238
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg239 chain
  [(0x8000f0c0#64, 0x1259583#32)]
    terminator ⟨0x8000f0c4#64, 0x1a40106f#32, 0x6f#8, 0x10#8, 0x40#8, 0x1a#8, .j, 0, 0, 0#13, 0x0011a4#21, 0#12⟩ ;;
  [(0x80010268#64, 0xff010113#32),
   (0x8001026c#64, 0x813023#32),
   (0x80010270#64, 0x50413#32),
   (0x80010274#64, 0x58513#32),
   (0x80010278#64, 0x4e01ac23#32),
   (0x8001027c#64, 0x113423#32)]

def traceLds239 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8]]

theorem facts239 : ChainFacts (writeLog snapshotMem traceD239.log)
    (writeLog snapshotMem traceD239.log) traceD239.regs traceLds239 traceSeg239 := by
  have kind0 : (mkLine 0x8000f0c0#64 0x1259583#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x80010268#64 0xff010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8001026c#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80010270#64 0x50413#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80010274#64 0x58513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80010278#64 0x4e01ac23#32).kind = MKind.sw := by decide
  have kind6 : (mkLine 0x8001027c#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg239, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run239 {c : Config} (h : TraceHolds traceD239 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD240 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg239 traceLds239 (by decide) facts239 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 251 ++ (evalBlocks traceSeg239 (SegEvalState.init traceD239.regs traceLds239)).log = traceStores.take 254
  have hw : (evalBlocks traceSeg239 (SegEvalState.init traceD239.regs traceLds239)).log = (traceStores.drop 251).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run239
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts240 : TraceCallFacts traceD240 0xe19ef0ef#32
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

theorem run240 {c : Config} (h : TraceHolds traceD240 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD241 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe19ef0ef#32 0x1efe18#21 0xef#8 0xf0#8 0x9e#8 0xe1#8 facts240 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run240
end Vsa.Sim.OutputAliasLoaded
