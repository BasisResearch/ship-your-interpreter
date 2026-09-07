import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part03
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part04
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part19
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part05
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part29
import Vsa.Sim.DecodeTable.Batch07Part30
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part18
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part29
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part11
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part14
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part06
import Vsa.Sim.DecodeTable.Batch11Part09
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch12Part05
import Vsa.Sim.DecodeTable.Batch13Part13
import Vsa.Sim.DecodeTable.Batch14Part12
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part24
import Vsa.Sim.DecodeTable.Batch15Part27
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.DecodeTable.Batch16Part29
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts141 : TraceCallFacts traceD141 0xf45ff0ef#32
    (instruction.JAL (0x1fff44#21, gprIdx 1)) 0xef#8 0xf0#8 0x5f#8 0xf4#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_f45ff0ef

theorem run141 {c : Config} (h : TraceHolds traceD141 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD142 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xf45ff0ef#32 0x1fff44#21 0xef#8 0xf0#8 0x5f#8 0xf4#8 facts141 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run141
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg142 chain
  [(0x80002ed4#64, 0xfb010113#32),
   (0x80002ed8#64, 0x3413023#32),
   (0x80002edc#64, 0x4113423#32),
   (0x80002ee0#64, 0x50a13#32)]
    terminator ⟨0x80002ee4#64, 0x06c05e63#32, 0x63#8, 0x5e#8, 0xc0#8, 0x06#8, .br bop.BGE true, 0, 12, 0x007c#13, 0#21, 0#12⟩ ;;
  [(0x80002f60#64, 0xa0513#32)]

def traceLds142 : List (List (BitVec 8)) :=
  []

theorem facts142 : ChainFacts (writeLog snapshotMem traceD142.log)
    (writeLog snapshotMem traceD142.log) traceD142.regs traceLds142 traceSeg142 := by
  have kind0 : (mkLine 0x80002ed4#64 0xfb010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002ed8#64 0x3413023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002edc#64 0x4113423#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80002ee0#64 0x50a13#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80002f60#64 0xa0513#32).kind = MKind.addi := by decide
  simp only [traceSeg142, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050a13
    | exact DecodeTable.decode_000a0513
    | exact DecodeTable.decode_03413023
    | exact DecodeTable.decode_04113423
    | exact DecodeTable.decode_06c05e63
    | exact DecodeTable.decode_fb010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run142 {c : Config} (h : TraceHolds traceD142 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD143 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg142 traceLds142 (by decide) facts142 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 169 ++ (evalBlocks traceSeg142 (SegEvalState.init traceD142.regs traceLds142)).log = traceStores.take 171
  have hw : (evalBlocks traceSeg142 (SegEvalState.init traceD142.regs traceLds142)).log = (traceStores.drop 169).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run142
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts143 : TraceCallFacts traceD143 0x889ff0ef#32
    (instruction.JAL (0x1ff888#21, gprIdx 1)) 0xef#8 0xf0#8 0x9f#8 0x88#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_889ff0ef

theorem run143 {c : Config} (h : TraceHolds traceD143 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD144 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x889ff0ef#32 0x1ff888#21 0xef#8 0xf0#8 0x9f#8 0x88#8 facts143 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run143
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg144 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds144 : List (List (BitVec 8)) :=
  []

theorem facts144 : ChainFacts (writeLog snapshotMem traceD144.log)
    (writeLog snapshotMem traceD144.log) traceD144.regs traceLds144 traceSeg144 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg144, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run144 {c : Config} (h : TraceHolds traceD144 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD145 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg144 traceLds144 (by decide) facts144 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 171 ++ (evalBlocks traceSeg144 (SegEvalState.init traceD144.regs traceLds144)).log = traceStores.take 173
  have hw : (evalBlocks traceSeg144 (SegEvalState.init traceD144.regs traceLds144)).log = (traceStores.drop 171).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run144
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg145 chain
  [(0x80002f68#64, 0x4813083#32),
   (0x80002f6c#64, 0xa0513#32),
   (0x80002f70#64, 0x2013a03#32),
   (0x80002f74#64, 0x5010113#32)]
    terminator ⟨0x80002f78#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds145 : List (List (BitVec 8)) :=
  [[0x94#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts145 : ChainFacts (writeLog snapshotMem traceD145.log)
    (writeLog snapshotMem traceD145.log) traceD145.regs traceLds145 traceSeg145 := by
  have kind0 : (mkLine 0x80002f68#64 0x4813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002f6c#64 0xa0513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002f70#64 0x2013a03#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002f74#64 0x5010113#32).kind = MKind.addi := by decide
  simp only [traceSeg145, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_000a0513
    | exact DecodeTable.decode_02013a03
    | exact DecodeTable.decode_04813083
    | exact DecodeTable.decode_05010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run145 {c : Config} (h : TraceHolds traceD145 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD146 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg145 traceLds145 (by decide) facts145 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 173 ++ (evalBlocks traceSeg145 (SegEvalState.init traceD145.regs traceLds145)).log = traceStores.take 173
  have hw : (evalBlocks traceSeg145 (SegEvalState.init traceD145.regs traceLds145)).log = (traceStores.drop 173).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run145
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg146 chain
  [(0x80002f94#64, 0x4601b783#32),
   (0x80002f98#64, 0xa00513#32),
   (0x80002f9c#64, 0x107b583#32)]

def traceLds146 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts146 : ChainFacts (writeLog snapshotMem traceD146.log)
    (writeLog snapshotMem traceD146.log) traceD146.regs traceLds146 traceSeg146 := by
  have kind0 : (mkLine 0x80002f94#64 0x4601b783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002f98#64 0xa00513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002f9c#64 0x107b583#32).kind = MKind.ld := by decide
  simp only [traceSeg146, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00a00513
    | exact DecodeTable.decode_0107b583
    | exact DecodeTable.decode_4601b783
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run146 {c : Config} (h : TraceHolds traceD146 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD147 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg146 traceLds146 (by decide) facts146 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 173 ++ (evalBlocks traceSeg146 (SegEvalState.init traceD146.regs traceLds146)).log = traceStores.take 173
  have hw : (evalBlocks traceSeg146 (SegEvalState.init traceD146.regs traceLds146)).log = (traceStores.drop 173).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run146
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts147 : TraceCallFacts traceD147 0x340030ef#32
    (instruction.JAL (0x3340#21, gprIdx 1)) 0xef#8 0x30#8 0x0#8 0x34#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_340030ef

theorem run147 {c : Config} (h : TraceHolds traceD147 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD148 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x340030ef#32 0x3340#21 0xef#8 0x30#8 0x0#8 0x34#8 facts147 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run147
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD148_01 : TraceData :=
  { pc := 0x800062fc#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x8001b538#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 175,
    out := #["\n"], payload := 0x0#4 }

def traceD148_02 : TraceData :=
  { pc := 0x80006304#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 175,
    out := #["\n"], payload := 0x0#4 }

def traceD148_03 : TraceData :=
  { pc := 0x80006310#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 175,
    out := #["\n"], payload := 0x0#4 }

def traceD148_04 : TraceData :=
  { pc := 0x80006380#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 175,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg148_00 chain
  [(0x800062e0#64, 0x4601b703#32),
   (0x800062e4#64, 0xfe010113#32),
   (0x800062e8#64, 0x813823#32),
   (0x800062ec#64, 0x113c23#32),
   (0x800062f0#64, 0x50693#32),
   (0x800062f4#64, 0x58413#32)]
    terminator ⟨0x800062f8#64, 0x00070663#32, 0x63#8, 0x06#8, 0x07#8, 0x00#8, .br bop.BEQ false, 14, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds148_00 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts148_00 : ChainFacts (writeLog snapshotMem traceD148.log)
    (writeLog snapshotMem traceD148.log) traceD148.regs traceLds148_00 traceSeg148_00 := by
  have kind0 : (mkLine 0x800062e0#64 0x4601b703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800062e4#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800062e8#64 0x813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x800062ec#64 0x113c23#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x800062f0#64 0x50693#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800062f4#64 0x58413#32).kind = MKind.addi := by decide
  simp only [traceSeg148_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050693
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00070663
    | exact DecodeTable.decode_00113c23
    | exact DecodeTable.decode_00813823
    | exact DecodeTable.decode_4601b703
    | exact DecodeTable.decode_fe010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run148_00 {c : Config} (h : TraceHolds traceD148 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD148_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg148_00 traceLds148_00 (by decide) facts148_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 173 ++ (evalBlocks traceSeg148_00 (SegEvalState.init traceD148.regs traceLds148_00)).log = traceStores.take 175
  have hw : (evalBlocks traceSeg148_00 (SegEvalState.init traceD148.regs traceLds148_00)).log = (traceStores.drop 173).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run148_00

#derive_case traceSeg148_01 chain
  [(0x800062fc#64, 0x4873783#32)]
    terminator ⟨0x80006300#64, 0x08078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x08#8, .br bop.BEQ false, 15, 0, 0x009c#13, 0#21, 0#12⟩

def traceLds148_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts148_01 : ChainFacts (writeLog snapshotMem traceD148_01.log)
    (writeLog snapshotMem traceD148_01.log) traceD148_01.regs traceLds148_01 traceSeg148_01 := by
  have kind0 : (mkLine 0x800062fc#64 0x4873783#32).kind = MKind.ld := by decide
  simp only [traceSeg148_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04873783
    | exact DecodeTable.decode_08078e63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run148_01 {c : Config} (h : TraceHolds traceD148_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD148_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg148_01 traceLds148_01 (by decide) facts148_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 175 ++ (evalBlocks traceSeg148_01 (SegEvalState.init traceD148_01.regs traceLds148_01)).log = traceStores.take 175
  have hw : (evalBlocks traceSeg148_01 (SegEvalState.init traceD148_01.regs traceLds148_01)).log = (traceStores.drop 175).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run148_01

#derive_case traceSeg148_02 chain
  [(0x80006304#64, 0xb042783#32),
   (0x80006308#64, 0x17f793#32)]
    terminator ⟨0x8000630c#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩

def traceLds148_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts148_02 : ChainFacts (writeLog snapshotMem traceD148_02.log)
    (writeLog snapshotMem traceD148_02.log) traceD148_02.regs traceLds148_02 traceSeg148_02 := by
  have kind0 : (mkLine 0x80006304#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80006308#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg148_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00079863
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_0b042783
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run148_02 {c : Config} (h : TraceHolds traceD148_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD148_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg148_02 traceLds148_02 (by decide) facts148_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 175 ++ (evalBlocks traceSeg148_02 (SegEvalState.init traceD148_02.regs traceLds148_02)).log = traceStores.take 175
  have hw : (evalBlocks traceSeg148_02 (SegEvalState.init traceD148_02.regs traceLds148_02)).log = (traceStores.drop 175).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run148_02

#derive_case traceSeg148_03 chain
  [(0x80006310#64, 0x1045783#32),
   (0x80006314#64, 0x2007f793#32)]
    terminator ⟨0x80006318#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0068#13, 0#21, 0#12⟩

def traceLds148_03 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts148_03 : ChainFacts (writeLog snapshotMem traceD148_03.log)
    (writeLog snapshotMem traceD148_03.log) traceD148_03.regs traceLds148_03 traceSeg148_03 := by
  have kind0 : (mkLine 0x80006310#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind1 : (mkLine 0x80006314#64 0x2007f793#32).kind = MKind.andi := by decide
  simp only [traceSeg148_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_06078463
    | exact DecodeTable.decode_2007f793
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run148_03 {c : Config} (h : TraceHolds traceD148_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD148_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg148_03 traceLds148_03 (by decide) facts148_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 175 ++ (evalBlocks traceSeg148_03 (SegEvalState.init traceD148_03.regs traceLds148_03)).log = traceStores.take 175
  have hw : (evalBlocks traceSeg148_03 (SegEvalState.init traceD148_03.regs traceLds148_03)).log = (traceStores.drop 175).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run148_03

#derive_case traceSeg148_04 chain
  [(0x80006380#64, 0xa043503#32),
   (0x80006384#64, 0xd13423#32),
   (0x80006388#64, 0xe13023#32)]

def traceLds148_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts148_04 : ChainFacts (writeLog snapshotMem traceD148_04.log)
    (writeLog snapshotMem traceD148_04.log) traceD148_04.regs traceLds148_04 traceSeg148_04 := by
  have kind0 : (mkLine 0x80006380#64 0xa043503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80006384#64 0xd13423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80006388#64 0xe13023#32).kind = MKind.sd := by decide
  simp only [traceSeg148_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00d13423
    | exact DecodeTable.decode_00e13023
    | exact DecodeTable.decode_0a043503
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run148_04 {c : Config} (h : TraceHolds traceD148_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD149 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg148_04 traceLds148_04 (by decide) facts148_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 175 ++ (evalBlocks traceSeg148_04 (SegEvalState.init traceD148_04.regs traceLds148_04)).log = traceStores.take 177
  have hw : (evalBlocks traceSeg148_04 (SegEvalState.init traceD148_04.regs traceLds148_04)).log = (traceStores.drop 175).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run148_04
theorem run148 {c : Config} (h : TraceHolds traceD148 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD149 c' := by
  obtain ⟨c0, s0, h0⟩ := run148_00 h
  obtain ⟨c1, s1, h1⟩ := run148_01 h0
  obtain ⟨c2, s2, h2⟩ := run148_02 h1
  obtain ⟨c3, s3, h3⟩ := run148_03 h2
  obtain ⟨c4, s4, h4⟩ := run148_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run148
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts149 : TraceCallFacts traceD149 0x455000ef#32
    (instruction.JAL (0xc54#21, gprIdx 1)) 0xef#8 0x0#8 0x50#8 0x45#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_455000ef

theorem run149 {c : Config} (h : TraceHolds traceD149 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD150 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x455000ef#32 0xc54#21 0xef#8 0x0#8 0x50#8 0x45#8 facts149 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run149
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg150 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds150 : List (List (BitVec 8)) :=
  []

theorem facts150 : ChainFacts (writeLog snapshotMem traceD150.log)
    (writeLog snapshotMem traceD150.log) traceD150.regs traceLds150 traceSeg150 := by
  simp only [traceSeg150, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run150 {c : Config} (h : TraceHolds traceD150 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD151 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg150 traceLds150 (by decide) facts150 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 177 ++ (evalBlocks traceSeg150 (SegEvalState.init traceD150.regs traceLds150)).log = traceStores.take 177
  have hw : (evalBlocks traceSeg150 (SegEvalState.init traceD150.regs traceLds150)).log = (traceStores.drop 177).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run150
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg151 chain
  [(0x80006390#64, 0x813683#32),
   (0x80006394#64, 0x13703#32)]
    terminator ⟨0x80006398#64, 0xf85ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf8#8, .j, 0, 0, 0#13, 0x1fff84#21, 0#12⟩ ;;
  [(0x8000631c#64, 0x70513#32),
   (0x80006320#64, 0x68593#32),
   (0x80006324#64, 0x40613#32)]

def traceLds151 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts151 : ChainFacts (writeLog snapshotMem traceD151.log)
    (writeLog snapshotMem traceD151.log) traceD151.regs traceLds151 traceSeg151 := by
  have kind0 : (mkLine 0x80006390#64 0x813683#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80006394#64 0x13703#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000631c#64 0x70513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006320#64 0x68593#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80006324#64 0x40613#32).kind = MKind.addi := by decide
  simp only [traceSeg151, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013703
    | exact DecodeTable.decode_00040613
    | exact DecodeTable.decode_00068593
    | exact DecodeTable.decode_00070513
    | exact DecodeTable.decode_00813683
    | exact DecodeTable.decode_f85ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run151 {c : Config} (h : TraceHolds traceD151 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD152 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg151 traceLds151 (by decide) facts151 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 177 ++ (evalBlocks traceSeg151 (SegEvalState.init traceD151.regs traceLds151)).log = traceStores.take 177
  have hw : (evalBlocks traceSeg151 (SegEvalState.init traceD151.regs traceLds151)).log = (traceStores.drop 177).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run151
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts152 : TraceCallFacts traceD152 0x37c080ef#32
    (instruction.JAL (0x837c#21, gprIdx 1)) 0xef#8 0x80#8 0xc0#8 0x37#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_37c080ef

theorem run152 {c : Config} (h : TraceHolds traceD152 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD153 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x37c080ef#32 0x837c#21 0xef#8 0x80#8 0xc0#8 0x37#8 facts152 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run152
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg153 chain
  [(0x8000e6a4#64, 0xfd010113#32),
   (0x8000e6a8#64, 0x2113423#32),
   (0x8000e6ac#64, 0x50713#32)]
    terminator ⟨0x8000e6b0#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩ ;;
  [(0x8000e6b4#64, 0x4853783#32)]
    terminator ⟨0x8000e6b8#64, 0x0c078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x0c#8, .br bop.BEQ false, 15, 0, 0x00d8#13, 0#21, 0#12⟩ ;;
  [(0x8000e6bc#64, 0xb062783#32),
   (0x8000e6c0#64, 0x17f793#32)]
    terminator ⟨0x8000e6c4#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000e6c8#64, 0x1065783#32),
   (0x8000e6cc#64, 0x2007f793#32)]
    terminator ⟨0x8000e6d0#64, 0x06078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x007c#13, 0#21, 0#12⟩ ;;
  [(0x8000e74c#64, 0xa063503#32),
   (0x8000e750#64, 0xb13c23#32),
   (0x8000e754#64, 0xe13823#32),
   (0x8000e758#64, 0xc13423#32)]

def traceLds153 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts153 : ChainFacts (writeLog snapshotMem traceD153.log)
    (writeLog snapshotMem traceD153.log) traceD153.regs traceLds153 traceSeg153 := by
  have kind0 : (mkLine 0x8000e6a4#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e6a8#64 0x2113423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000e6ac#64 0x50713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000e6b4#64 0x4853783#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x8000e6bc#64 0xb062783#32).kind = MKind.lw := by decide
  have kind5 : (mkLine 0x8000e6c0#64 0x17f793#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000e6c8#64 0x1065783#32).kind = MKind.lhu := by decide
  have kind7 : (mkLine 0x8000e6cc#64 0x2007f793#32).kind = MKind.andi := by decide
  have kind8 : (mkLine 0x8000e74c#64 0xa063503#32).kind = MKind.ld := by decide
  have kind9 : (mkLine 0x8000e750#64 0xb13c23#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x8000e754#64 0xe13823#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x8000e758#64 0xc13423#32).kind = MKind.sd := by decide
  simp only [traceSeg153, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050663
    | exact DecodeTable.decode_00050713
    | exact DecodeTable.decode_00079863
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_00b13c23
    | exact DecodeTable.decode_00c13423
    | exact DecodeTable.decode_00e13823
    | exact DecodeTable.decode_01065783
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_04853783
    | exact DecodeTable.decode_06078e63
    | exact DecodeTable.decode_0a063503
    | exact DecodeTable.decode_0b062783
    | exact DecodeTable.decode_0c078c63
    | exact DecodeTable.decode_2007f793
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run153 {c : Config} (h : TraceHolds traceD153 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD154 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg153 traceLds153 (by decide) facts153 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 177 ++ (evalBlocks traceSeg153 (SegEvalState.init traceD153.regs traceLds153)).log = traceStores.take 181
  have hw : (evalBlocks traceSeg153 (SegEvalState.init traceD153.regs traceLds153)).log = (traceStores.drop 177).take 4 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run153
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts154 : TraceCallFacts traceD154 0x885f80ef#32
    (instruction.JAL (0x1f8884#21, gprIdx 1)) 0xef#8 0x80#8 0x5f#8 0x88#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_885f80ef

theorem run154 {c : Config} (h : TraceHolds traceD154 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD155 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x885f80ef#32 0x1f8884#21 0xef#8 0x80#8 0x5f#8 0x88#8 facts154 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run154
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg155 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds155 : List (List (BitVec 8)) :=
  []

theorem facts155 : ChainFacts (writeLog snapshotMem traceD155.log)
    (writeLog snapshotMem traceD155.log) traceD155.regs traceLds155 traceSeg155 := by
  simp only [traceSeg155, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run155 {c : Config} (h : TraceHolds traceD155 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD156 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg155 traceLds155 (by decide) facts155 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 181 ++ (evalBlocks traceSeg155 (SegEvalState.init traceD155.regs traceLds155)).log = traceStores.take 181
  have hw : (evalBlocks traceSeg155 (SegEvalState.init traceD155.regs traceLds155)).log = (traceStores.drop 181).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run155
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg156 chain
  [(0x8000e760#64, 0x1813583#32),
   (0x8000e764#64, 0x1013703#32),
   (0x8000e768#64, 0x813603#32)]
    terminator ⟨0x8000e76c#64, 0xf69ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xf6#8, .j, 0, 0, 0#13, 0x1fff68#21, 0#12⟩ ;;
  [(0x8000e6d4#64, 0xc62783#32),
   (0x8000e6d8#64, 0xff5f693#32),
   (0x8000e6dc#64, 0xfff7879b#32),
   (0x8000e6e0#64, 0xf62623#32)]
    terminator ⟨0x8000e6e4#64, 0x0007da63#32, 0x63#8, 0xda#8, 0x07#8, 0x00#8, .br bop.BGE false, 15, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8000e6e8#64, 0x2862503#32)]
    terminator ⟨0x8000e6ec#64, 0x04a7c463#32, 0x63#8, 0xc4#8, 0xa7#8, 0x04#8, .br bop.BLT true, 15, 10, 0x0048#13, 0#21, 0#12⟩ ;;
  [(0x8000e734#64, 0x70513#32),
   (0x8000e738#64, 0xc13423#32)]

def traceLds156 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts156 : ChainFacts (writeLog snapshotMem traceD156.log)
    (writeLog snapshotMem traceD156.log) traceD156.regs traceLds156 traceSeg156 := by
  have kind0 : (mkLine 0x8000e760#64 0x1813583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e764#64 0x1013703#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e768#64 0x813603#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000e6d4#64 0xc62783#32).kind = MKind.lw := by decide
  have kind4 : (mkLine 0x8000e6d8#64 0xff5f693#32).kind = MKind.andi := by decide
  have kind5 : (mkLine 0x8000e6dc#64 0xfff7879b#32).kind = MKind.addiw := by decide
  have kind6 : (mkLine 0x8000e6e0#64 0xf62623#32).kind = MKind.sw := by decide
  have kind7 : (mkLine 0x8000e6e8#64 0x2862503#32).kind = MKind.lw := by decide
  have kind8 : (mkLine 0x8000e734#64 0x70513#32).kind = MKind.addi := by decide
  have kind9 : (mkLine 0x8000e738#64 0xc13423#32).kind = MKind.sd := by decide
  simp only [traceSeg156, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00070513
    | exact DecodeTable.decode_0007da63
    | exact DecodeTable.decode_00813603
    | exact DecodeTable.decode_00c13423
    | exact DecodeTable.decode_00c62783
    | exact DecodeTable.decode_00f62623
    | exact DecodeTable.decode_01013703
    | exact DecodeTable.decode_01813583
    | exact DecodeTable.decode_02862503
    | exact DecodeTable.decode_04a7c463
    | exact DecodeTable.decode_0ff5f693
    | exact DecodeTable.decode_f69ff06f
    | exact DecodeTable.decode_fff7879b
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run156 {c : Config} (h : TraceHolds traceD156 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD157 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg156 traceLds156 (by decide) facts156 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 181 ++ (evalBlocks traceSeg156 (SegEvalState.init traceD156.regs traceLds156)).log = traceStores.take 183
  have hw : (evalBlocks traceSeg156 (SegEvalState.init traceD156.regs traceLds156)).log = (traceStores.drop 181).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run156
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts157 : TraceCallFacts traceD157 0x18d000ef#32
    (instruction.JAL (0x98c#21, gprIdx 1)) 0xef#8 0x0#8 0xd0#8 0x18#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_18d000ef

theorem run157 {c : Config} (h : TraceHolds traceD157 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x18d000ef#32 0x98c#21 0xef#8 0x0#8 0xd0#8 0x18#8 facts157 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run157
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD158_01 : TraceData :=
  { pc := 0x8000f0e4#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0xffffffffffffffff#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 186,
    out := #["\n"], payload := 0x0#4 }

def traceD158_02 : TraceData :=
  { pc := 0x8000f0ec#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 186,
    out := #["\n"], payload := 0x0#4 }

def traceD158_03 : TraceData :=
  { pc := 0x8000f100#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 187,
    out := #["\n"], payload := 0x0#4 }

def traceD158_04 : TraceData :=
  { pc := 0x8000f108#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001bb97#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 187,
    out := #["\n"], payload := 0x0#4 }

def traceD158_05 : TraceData :=
  { pc := 0x8000f118#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x8028000000000000#64), (14, 0x0#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 187,
    out := #["\n"], payload := 0x0#4 }

def traceD158_06 : TraceData :=
  { pc := 0x8000f120#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x8028000000000000#64), (14, 0x0#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 187,
    out := #["\n"], payload := 0x0#4 }

def traceD158_07 : TraceData :=
  { pc := 0x8000f134#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x1#64), (14, 0x8001bb97#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 187,
    out := #["\n"], payload := 0x0#4 }

def traceD158_08 : TraceData :=
  { pc := 0x8000f154#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb98#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x1#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 190,
    out := #["\n"], payload := 0x0#4 }

def traceD158_09 : TraceData :=
  { pc := 0x8000f1d0#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb98#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x1#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 190,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg158_00 chain
  [(0x8000f0c8#64, 0xfd010113#32),
   (0x8000f0cc#64, 0x2813023#32),
   (0x8000f0d0#64, 0x913c23#32),
   (0x8000f0d4#64, 0x2113423#32),
   (0x8000f0d8#64, 0x50493#32),
   (0x8000f0dc#64, 0x58413#32)]
    terminator ⟨0x8000f0e0#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds158_00 : List (List (BitVec 8)) :=
  []

theorem facts158_00 : ChainFacts (writeLog snapshotMem traceD158.log)
    (writeLog snapshotMem traceD158.log) traceD158.regs traceLds158_00 traceSeg158_00 := by
  have kind0 : (mkLine 0x8000f0c8#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f0cc#64 0x2813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000f0d0#64 0x913c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000f0d4#64 0x2113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000f0d8#64 0x50493#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x8000f0dc#64 0x58413#32).kind = MKind.addi := by decide
  simp only [traceSeg158_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00050663
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00913c23
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_02813023
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_00 {c : Config} (h : TraceHolds traceD158 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_00 traceLds158_00 (by decide) facts158_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 183 ++ (evalBlocks traceSeg158_00 (SegEvalState.init traceD158.regs traceLds158_00)).log = traceStores.take 186
  have hw : (evalBlocks traceSeg158_00 (SegEvalState.init traceD158.regs traceLds158_00)).log = (traceStores.drop 183).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_00

#derive_case traceSeg158_01 chain
  [(0x8000f0e4#64, 0x4853783#32)]
    terminator ⟨0x8000f0e8#64, 0x12078263#32, 0x63#8, 0x82#8, 0x07#8, 0x12#8, .br bop.BEQ false, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds158_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts158_01 : ChainFacts (writeLog snapshotMem traceD158_01.log)
    (writeLog snapshotMem traceD158_01.log) traceD158_01.regs traceLds158_01 traceSeg158_01 := by
  have kind0 : (mkLine 0x8000f0e4#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg158_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact DecodeTable.decode_12078263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_01 {c : Config} (h : TraceHolds traceD158_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_01 traceLds158_01 (by decide) facts158_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 186 ++ (evalBlocks traceSeg158_01 (SegEvalState.init traceD158_01.regs traceLds158_01)).log = traceStores.take 186
  have hw : (evalBlocks traceSeg158_01 (SegEvalState.init traceD158_01.regs traceLds158_01)).log = (traceStores.drop 186).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_01

#derive_case traceSeg158_02 chain
  [(0x8000f0ec#64, 0x2862703#32),
   (0x8000f0f0#64, 0x1061783#32),
   (0x8000f0f4#64, 0xe62623#32),
   (0x8000f0f8#64, 0x87f713#32)]
    terminator ⟨0x8000f0fc#64, 0x08070663#32, 0x63#8, 0x06#8, 0x07#8, 0x08#8, .br bop.BEQ false, 14, 0, 0x008c#13, 0#21, 0#12⟩

def traceLds158_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8]]

theorem facts158_02 : ChainFacts (writeLog snapshotMem traceD158_02.log)
    (writeLog snapshotMem traceD158_02.log) traceD158_02.regs traceLds158_02 traceSeg158_02 := by
  have kind0 : (mkLine 0x8000f0ec#64 0x2862703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000f0f0#64 0x1061783#32).kind = MKind.lh := by decide
  have kind2 : (mkLine 0x8000f0f4#64 0xe62623#32).kind = MKind.sw := by decide
  have kind3 : (mkLine 0x8000f0f8#64 0x87f713#32).kind = MKind.andi := by decide
  simp only [traceSeg158_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0087f713
    | exact DecodeTable.decode_00e62623
    | exact DecodeTable.decode_01061783
    | exact DecodeTable.decode_02862703
    | exact DecodeTable.decode_08070663
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_02 {c : Config} (h : TraceHolds traceD158_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_02 traceLds158_02 (by decide) facts158_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 186 ++ (evalBlocks traceSeg158_02 (SegEvalState.init traceD158_02.regs traceLds158_02)).log = traceStores.take 187
  have hw : (evalBlocks traceSeg158_02 (SegEvalState.init traceD158_02.regs traceLds158_02)).log = (traceStores.drop 186).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_02

#derive_case traceSeg158_03 chain
  [(0x8000f100#64, 0x1863703#32)]
    terminator ⟨0x8000f104#64, 0x08070263#32, 0x63#8, 0x02#8, 0x07#8, 0x08#8, .br bop.BEQ false, 14, 0, 0x0084#13, 0#21, 0#12⟩

def traceLds158_03 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts158_03 : ChainFacts (writeLog snapshotMem traceD158_03.log)
    (writeLog snapshotMem traceD158_03.log) traceD158_03.regs traceLds158_03 traceSeg158_03 := by
  have kind0 : (mkLine 0x8000f100#64 0x1863703#32).kind = MKind.ld := by decide
  simp only [traceSeg158_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01863703
    | exact DecodeTable.decode_08070263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_03 {c : Config} (h : TraceHolds traceD158_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_03 traceLds158_03 (by decide) facts158_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 187 ++ (evalBlocks traceSeg158_03 (SegEvalState.init traceD158_03.regs traceLds158_03)).log = traceStores.take 187
  have hw : (evalBlocks traceSeg158_03 (SegEvalState.init traceD158_03.regs traceLds158_03)).log = (traceStores.drop 187).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_03

#derive_case traceSeg158_04 chain
  [(0x8000f108#64, 0x3279693#32),
   (0x8000f10c#64, 0xb062703#32),
   (0x8000f110#64, 0x25b7#32)]
    terminator ⟨0x8000f114#64, 0x0a06d063#32, 0x63#8, 0xd0#8, 0x06#8, 0x0a#8, .br bop.BGE false, 13, 0, 0x00a0#13, 0#21, 0#12⟩

def traceLds158_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts158_04 : ChainFacts (writeLog snapshotMem traceD158_04.log)
    (writeLog snapshotMem traceD158_04.log) traceD158_04.regs traceLds158_04 traceSeg158_04 := by
  have kind0 : (mkLine 0x8000f108#64 0x3279693#32).kind = MKind.slli := by decide
  have kind1 : (mkLine 0x8000f10c#64 0xb062703#32).kind = MKind.lw := by decide
  have kind2 : (mkLine 0x8000f110#64 0x25b7#32).kind = MKind.lui := by decide
  simp only [traceSeg158_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_000025b7
    | exact DecodeTable.decode_03279693
    | exact DecodeTable.decode_0a06d063
    | exact DecodeTable.decode_0b062703
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_04 {c : Config} (h : TraceHolds traceD158_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_04 traceLds158_04 (by decide) facts158_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 187 ++ (evalBlocks traceSeg158_04 (SegEvalState.init traceD158_04.regs traceLds158_04)).log = traceStores.take 187
  have hw : (evalBlocks traceSeg158_04 (SegEvalState.init traceD158_04.regs traceLds158_04)).log = (traceStores.drop 187).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_04

#derive_case traceSeg158_05 chain
  [(0x8000f118#64, 0x3271793#32)]
    terminator ⟨0x8000f11c#64, 0x0c07c263#32, 0x63#8, 0xc2#8, 0x07#8, 0x0c#8, .br bop.BLT false, 15, 0, 0x00c4#13, 0#21, 0#12⟩

def traceLds158_05 : List (List (BitVec 8)) :=
  []

theorem facts158_05 : ChainFacts (writeLog snapshotMem traceD158_05.log)
    (writeLog snapshotMem traceD158_05.log) traceD158_05.regs traceLds158_05 traceSeg158_05 := by
  have kind0 : (mkLine 0x8000f118#64 0x3271793#32).kind = MKind.slli := by decide
  simp only [traceSeg158_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_03271793
    | exact DecodeTable.decode_0c07c263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_05 {c : Config} (h : TraceHolds traceD158_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_05 traceLds158_05 (by decide) facts158_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 187 ++ (evalBlocks traceSeg158_05 (SegEvalState.init traceD158_05.regs traceLds158_05)).log = traceStores.take 187
  have hw : (evalBlocks traceSeg158_05 (SegEvalState.init traceD158_05.regs traceLds158_05)).log = (traceStores.drop 187).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_05

#derive_case traceSeg158_06 chain
  [(0x8000f120#64, 0x63703#32),
   (0x8000f124#64, 0x1863783#32),
   (0x8000f128#64, 0x2062683#32),
   (0x8000f12c#64, 0x40f707bb#32)]
    terminator ⟨0x8000f130#64, 0x0ad7dc63#32, 0x63#8, 0xdc#8, 0xd7#8, 0x0a#8, .br bop.BGE false, 15, 13, 0x00b8#13, 0#21, 0#12⟩

def traceLds158_06 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts158_06 : ChainFacts (writeLog snapshotMem traceD158_06.log)
    (writeLog snapshotMem traceD158_06.log) traceD158_06.regs traceLds158_06 traceSeg158_06 := by
  have kind0 : (mkLine 0x8000f120#64 0x63703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000f124#64 0x1863783#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000f128#64 0x2062683#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000f12c#64 0x40f707bb#32).kind = MKind.subw := by decide
  simp only [traceSeg158_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00063703
    | exact DecodeTable.decode_01863783
    | exact DecodeTable.decode_02062683
    | exact DecodeTable.decode_0ad7dc63
    | exact DecodeTable.decode_40f707bb
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_06 {c : Config} (h : TraceHolds traceD158_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_06 traceLds158_06 (by decide) facts158_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 187 ++ (evalBlocks traceSeg158_06 (SegEvalState.init traceD158_06.regs traceLds158_06)).log = traceStores.take 187
  have hw : (evalBlocks traceSeg158_06 (SegEvalState.init traceD158_06.regs traceLds158_06)).log = (traceStores.drop 187).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_06

#derive_case traceSeg158_07 chain
  [(0x8000f134#64, 0x17879b#32),
   (0x8000f138#64, 0xc62683#32),
   (0x8000f13c#64, 0x170593#32),
   (0x8000f140#64, 0xb63023#32),
   (0x8000f144#64, 0xfff6869b#32),
   (0x8000f148#64, 0xd62623#32),
   (0x8000f14c#64, 0x870023#32),
   (0x8000f150#64, 0x2062703#32)]

def traceLds158_07 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts158_07 : ChainFacts (writeLog snapshotMem traceD158_07.log)
    (writeLog snapshotMem traceD158_07.log) traceD158_07.regs traceLds158_07 traceSeg158_07 := by
  have kind0 : (mkLine 0x8000f134#64 0x17879b#32).kind = MKind.addiw := by decide
  have kind1 : (mkLine 0x8000f138#64 0xc62683#32).kind = MKind.lw := by decide
  have kind2 : (mkLine 0x8000f13c#64 0x170593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000f140#64 0xb63023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000f144#64 0xfff6869b#32).kind = MKind.addiw := by decide
  have kind5 : (mkLine 0x8000f148#64 0xd62623#32).kind = MKind.sw := by decide
  have kind6 : (mkLine 0x8000f14c#64 0x870023#32).kind = MKind.sb := by decide
  have kind7 : (mkLine 0x8000f150#64 0x2062703#32).kind = MKind.lw := by decide
  simp only [traceSeg158_07, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00170593
    | exact DecodeTable.decode_0017879b
    | exact DecodeTable.decode_00870023
    | exact DecodeTable.decode_00b63023
    | exact DecodeTable.decode_00c62683
    | exact DecodeTable.decode_00d62623
    | exact DecodeTable.decode_02062703
    | exact DecodeTable.decode_fff6869b
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_07 {c : Config} (h : TraceHolds traceD158_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_08 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_07 traceLds158_07 (by decide) facts158_07 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 187 ++ (evalBlocks traceSeg158_07 (SegEvalState.init traceD158_07.regs traceLds158_07)).log = traceStores.take 190
  have hw : (evalBlocks traceSeg158_07 (SegEvalState.init traceD158_07.regs traceLds158_07)).log = (traceStores.drop 187).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_07

#derive_case traceSeg158_08 chain
  [(0x8000f154#64, 0xff47413#32)]
    terminator ⟨0x8000f158#64, 0x06f70c63#32, 0x63#8, 0x0c#8, 0xf7#8, 0x06#8, .br bop.BEQ true, 14, 15, 0x0078#13, 0#21, 0#12⟩

def traceLds158_08 : List (List (BitVec 8)) :=
  []

theorem facts158_08 : ChainFacts (writeLog snapshotMem traceD158_08.log)
    (writeLog snapshotMem traceD158_08.log) traceD158_08.regs traceLds158_08 traceSeg158_08 := by
  have kind0 : (mkLine 0x8000f154#64 0xff47413#32).kind = MKind.andi := by decide
  simp only [traceSeg158_08, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_06f70c63
    | exact DecodeTable.decode_0ff47413
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_08 {c : Config} (h : TraceHolds traceD158_08 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD158_09 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_08 traceLds158_08 (by decide) facts158_08 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 190 ++ (evalBlocks traceSeg158_08 (SegEvalState.init traceD158_08.regs traceLds158_08)).log = traceStores.take 190
  have hw : (evalBlocks traceSeg158_08 (SegEvalState.init traceD158_08.regs traceLds158_08)).log = (traceStores.drop 190).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_08

#derive_case traceSeg158_09 chain
  [(0x8000f1d0#64, 0x60593#32),
   (0x8000f1d4#64, 0x48513#32)]

def traceLds158_09 : List (List (BitVec 8)) :=
  []

theorem facts158_09 : ChainFacts (writeLog snapshotMem traceD158_09.log)
    (writeLog snapshotMem traceD158_09.log) traceD158_09.regs traceLds158_09 traceSeg158_09 := by
  have kind0 : (mkLine 0x8000f1d0#64 0x60593#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f1d4#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg158_09, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00060593
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run158_09 {c : Config} (h : TraceHolds traceD158_09 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD159 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg158_09 traceLds158_09 (by decide) facts158_09 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 190 ++ (evalBlocks traceSeg158_09 (SegEvalState.init traceD158_09.regs traceLds158_09)).log = traceStores.take 190
  have hw : (evalBlocks traceSeg158_09 (SegEvalState.init traceD158_09.regs traceLds158_09)).log = (traceStores.drop 190).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run158_09
theorem run158 {c : Config} (h : TraceHolds traceD158 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD159 c' := by
  obtain ⟨c0, s0, h0⟩ := run158_00 h
  obtain ⟨c1, s1, h1⟩ := run158_01 h0
  obtain ⟨c2, s2, h2⟩ := run158_02 h1
  obtain ⟨c3, s3, h3⟩ := run158_03 h2
  obtain ⟨c4, s4, h4⟩ := run158_04 h3
  obtain ⟨c5, s5, h5⟩ := run158_05 h4
  obtain ⟨c6, s6, h6⟩ := run158_06 h5
  obtain ⟨c7, s7, h7⟩ := run158_07 h6
  obtain ⟨c8, s8, h8⟩ := run158_08 h7
  obtain ⟨c9, s9, h9⟩ := run158_09 h8
  exact ⟨c9, (((((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9, h9⟩

#print axioms run158
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts159 : TraceCallFacts traceD159 0xbf5ff0ef#32
    (instruction.JAL (0x1ffbf4#21, gprIdx 1)) 0xef#8 0xf0#8 0x5f#8 0xbf#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_bf5ff0ef

theorem run159 {c : Config} (h : TraceHolds traceD159 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xbf5ff0ef#32 0x1ffbf4#21 0xef#8 0xf0#8 0x5f#8 0xbf#8 facts159 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run159
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD160_01 : TraceData :=
  { pc := 0x8000eddc#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x8001b538#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 191,
    out := #["\n"], payload := 0x0#4 }

def traceD160_02 : TraceData :=
  { pc := 0x8000ede4#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 191,
    out := #["\n"], payload := 0x0#4 }

def traceD160_03 : TraceData :=
  { pc := 0x8000edf0#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x200a#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 191,
    out := #["\n"], payload := 0x0#4 }

def traceD160_04 : TraceData :=
  { pc := 0x8000edfc#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x200a#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 191,
    out := #["\n"], payload := 0x0#4 }

def traceD160_05 : TraceData :=
  { pc := 0x8000ee40#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 191,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg160_00 chain
  [(0x8000edcc#64, 0xfe010113#32),
   (0x8000edd0#64, 0x113c23#32),
   (0x8000edd4#64, 0x50713#32)]
    terminator ⟨0x8000edd8#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds160_00 : List (List (BitVec 8)) :=
  []

theorem facts160_00 : ChainFacts (writeLog snapshotMem traceD160.log)
    (writeLog snapshotMem traceD160.log) traceD160.regs traceLds160_00 traceSeg160_00 := by
  have kind0 : (mkLine 0x8000edcc#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000edd0#64 0x113c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000edd4#64 0x50713#32).kind = MKind.addi := by decide
  simp only [traceSeg160_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050663
    | exact DecodeTable.decode_00050713
    | exact DecodeTable.decode_00113c23
    | exact DecodeTable.decode_fe010113
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_00 {c : Config} (h : TraceHolds traceD160 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_00 traceLds160_00 (by decide) facts160_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 190 ++ (evalBlocks traceSeg160_00 (SegEvalState.init traceD160.regs traceLds160_00)).log = traceStores.take 191
  have hw : (evalBlocks traceSeg160_00 (SegEvalState.init traceD160.regs traceLds160_00)).log = (traceStores.drop 190).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_00

#derive_case traceSeg160_01 chain
  [(0x8000eddc#64, 0x4853783#32)]
    terminator ⟨0x8000ede0#64, 0x08078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x08#8, .br bop.BEQ false, 15, 0, 0x009c#13, 0#21, 0#12⟩

def traceLds160_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts160_01 : ChainFacts (writeLog snapshotMem traceD160_01.log)
    (writeLog snapshotMem traceD160_01.log) traceD160_01.regs traceLds160_01 traceSeg160_01 := by
  have kind0 : (mkLine 0x8000eddc#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg160_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact DecodeTable.decode_08078e63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_01 {c : Config} (h : TraceHolds traceD160_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_01 traceLds160_01 (by decide) facts160_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 191 ++ (evalBlocks traceSeg160_01 (SegEvalState.init traceD160_01.regs traceLds160_01)).log = traceStores.take 191
  have hw : (evalBlocks traceSeg160_01 (SegEvalState.init traceD160_01.regs traceLds160_01)).log = (traceStores.drop 191).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_01

#derive_case traceSeg160_02 chain
  [(0x8000ede4#64, 0x1059683#32),
   (0x8000ede8#64, 0x793#32)]
    terminator ⟨0x8000edec#64, 0x04068263#32, 0x63#8, 0x82#8, 0x06#8, 0x04#8, .br bop.BEQ false, 13, 0, 0x0044#13, 0#21, 0#12⟩

def traceLds160_02 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts160_02 : ChainFacts (writeLog snapshotMem traceD160_02.log)
    (writeLog snapshotMem traceD160_02.log) traceD160_02.regs traceLds160_02 traceSeg160_02 := by
  have kind0 : (mkLine 0x8000ede4#64 0x1059683#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000ede8#64 0x793#32).kind = MKind.addi := by decide
  simp only [traceSeg160_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000793
    | exact DecodeTable.decode_01059683
    | exact DecodeTable.decode_04068263
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_02 {c : Config} (h : TraceHolds traceD160_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_02 traceLds160_02 (by decide) facts160_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 191 ++ (evalBlocks traceSeg160_02 (SegEvalState.init traceD160_02.regs traceLds160_02)).log = traceStores.take 191
  have hw : (evalBlocks traceSeg160_02 (SegEvalState.init traceD160_02.regs traceLds160_02)).log = (traceStores.drop 191).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_02

#derive_case traceSeg160_03 chain
  [(0x8000edf0#64, 0xb05a783#32),
   (0x8000edf4#64, 0x17f793#32)]
    terminator ⟨0x8000edf8#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds160_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts160_03 : ChainFacts (writeLog snapshotMem traceD160_03.log)
    (writeLog snapshotMem traceD160_03.log) traceD160_03.regs traceLds160_03 traceSeg160_03 := by
  have kind0 : (mkLine 0x8000edf0#64 0xb05a783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000edf4#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg160_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00079663
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_0b05a783
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_03 {c : Config} (h : TraceHolds traceD160_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_03 traceLds160_03 (by decide) facts160_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 191 ++ (evalBlocks traceSeg160_03 (SegEvalState.init traceD160_03.regs traceLds160_03)).log = traceStores.take 191
  have hw : (evalBlocks traceSeg160_03 (SegEvalState.init traceD160_03.regs traceLds160_03)).log = (traceStores.drop 191).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_03

#derive_case traceSeg160_04 chain
  [(0x8000edfc#64, 0x2006f693#32)]
    terminator ⟨0x8000ee00#64, 0x04068063#32, 0x63#8, 0x80#8, 0x06#8, 0x04#8, .br bop.BEQ true, 13, 0, 0x0040#13, 0#21, 0#12⟩

def traceLds160_04 : List (List (BitVec 8)) :=
  []

theorem facts160_04 : ChainFacts (writeLog snapshotMem traceD160_04.log)
    (writeLog snapshotMem traceD160_04.log) traceD160_04.regs traceLds160_04 traceSeg160_04 := by
  have kind0 : (mkLine 0x8000edfc#64 0x2006f693#32).kind = MKind.andi := by decide
  simp only [traceSeg160_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04068063
    | exact DecodeTable.decode_2006f693
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_04 {c : Config} (h : TraceHolds traceD160_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD160_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_04 traceLds160_04 (by decide) facts160_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 191 ++ (evalBlocks traceSeg160_04 (SegEvalState.init traceD160_04.regs traceLds160_04)).log = traceStores.take 191
  have hw : (evalBlocks traceSeg160_04 (SegEvalState.init traceD160_04.regs traceLds160_04)).log = (traceStores.drop 191).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_04

#derive_case traceSeg160_05 chain
  [(0x8000ee40#64, 0xa05b503#32),
   (0x8000ee44#64, 0xe13423#32),
   (0x8000ee48#64, 0xb13023#32)]

def traceLds160_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts160_05 : ChainFacts (writeLog snapshotMem traceD160_05.log)
    (writeLog snapshotMem traceD160_05.log) traceD160_05.regs traceLds160_05 traceSeg160_05 := by
  have kind0 : (mkLine 0x8000ee40#64 0xa05b503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee44#64 0xe13423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ee48#64 0xb13023#32).kind = MKind.sd := by decide
  simp only [traceSeg160_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00b13023
    | exact DecodeTable.decode_00e13423
    | exact DecodeTable.decode_0a05b503
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run160_05 {c : Config} (h : TraceHolds traceD160_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD161 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg160_05 traceLds160_05 (by decide) facts160_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 191 ++ (evalBlocks traceSeg160_05 (SegEvalState.init traceD160_05.regs traceLds160_05)).log = traceStores.take 193
  have hw : (evalBlocks traceSeg160_05 (SegEvalState.init traceD160_05.regs traceLds160_05)).log = (traceStores.drop 191).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run160_05
theorem run160 {c : Config} (h : TraceHolds traceD160 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD161 c' := by
  obtain ⟨c0, s0, h0⟩ := run160_00 h
  obtain ⟨c1, s1, h1⟩ := run160_01 h0
  obtain ⟨c2, s2, h2⟩ := run160_02 h1
  obtain ⟨c3, s3, h3⟩ := run160_03 h2
  obtain ⟨c4, s4, h4⟩ := run160_04 h3
  obtain ⟨c5, s5, h5⟩ := run160_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run160
end Vsa.Sim.OutputAliasLoaded
