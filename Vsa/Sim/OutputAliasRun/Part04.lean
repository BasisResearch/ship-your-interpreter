import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part05
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch06Part03
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part28
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch11Part28
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch14Part13
import Vsa.Sim.DecodeTable.Batch14Part17
import Vsa.Sim.DecodeTable.Batch14Part18
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch15Part24
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts081 : TraceCallFacts traceD081 0xb90fe0ef#32
    (instruction.JAL (0x1fe390#21, gprIdx 1)) 0xef#8 0xe0#8 0xf#8 0xb9#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_b90fe0ef

theorem run081 {c : Config} (h : TraceHolds traceD081 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD082 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb90fe0ef#32 0x1fe390#21 0xef#8 0xe0#8 0xf#8 0xb9#8 facts081 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run081
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg082 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds082 : List (List (BitVec 8)) :=
  []

theorem facts082 : ChainFacts (writeLog snapshotMem traceD082.log)
    (writeLog snapshotMem traceD082.log) traceD082.regs traceLds082 traceSeg082 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg082, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run082 {c : Config} (h : TraceHolds traceD082 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD083 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg082 traceLds082 (by decide) facts082 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run082
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg083 chain
  [(0x80004460#64, 0x13783#32),
   (0x80004464#64, 0x5810693#32),
   (0x80004468#64, 0x48593#32),
   (0x8000446c#64, 0x7b603#32),
   (0x80004470#64, 0x78513#32)]

def traceLds083 : List (List (BitVec 8)) :=
  [[0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts083 : ChainFacts (writeLog snapshotMem traceD083.log)
    (writeLog snapshotMem traceD083.log) traceD083.regs traceLds083 traceSeg083 := by
  have kind0 : (mkLine 0x80004460#64 0x13783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004464#64 0x5810693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004468#64 0x48593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000446c#64 0x7b603#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004470#64 0x78513#32).kind = MKind.addi := by decide
  simp only [traceSeg083, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013783
    | exact DecodeTable.decode_00048593
    | exact DecodeTable.decode_00078513
    | exact DecodeTable.decode_0007b603
    | exact DecodeTable.decode_05810693
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run083 {c : Config} (h : TraceHolds traceD083 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD084 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg083 traceLds083 (by decide) facts083 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run083
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts084 : TraceCallFacts traceD084 0xb6dff0ef#32
    (instruction.JAL (0x1ffb6c#21, gprIdx 1)) 0xef#8 0xf0#8 0xdf#8 0xb6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_b6dff0ef

theorem run084 {c : Config} (h : TraceHolds traceD084 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD085 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb6dff0ef#32 0x1ffb6c#21 0xef#8 0xf0#8 0xdf#8 0xb6#8 facts084 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run084
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD085_01 : TraceData :=
  { pc := 0x80004000#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffba0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000040#64), (9, 0x87fffe10#64), (10, 0x87fffe10#64), (11, 0x82000040#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0xa#64), (15, 0x87fffe10#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 110,
    out := #["\n"], payload := 0x0#4 }

def traceD085_02 : TraceData :=
  { pc := 0x8000401c#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffba0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000040#64), (9, 0x87fffe10#64), (10, 0x87fffe10#64), (11, 0x82000040#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x80019fb8#64), (15, 0x3#64), (16, 0x8#64), (17, 0x8001bb97#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 110,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg085_00 chain
  [(0x80003fe0#64, 0xf5010113#32),
   (0x80003fe4#64, 0xa813023#32),
   (0x80003fe8#64, 0x8913c23#32),
   (0x80003fec#64, 0x9213823#32),
   (0x80003ff0#64, 0x9313423#32),
   (0x80003ff4#64, 0xa113423#32),
   (0x80003ff8#64, 0x58413#32),
   (0x80003ffc#64, 0x50493#32)]

def traceLds085_00 : List (List (BitVec 8)) :=
  []

theorem facts085_00 : ChainFacts (writeLog snapshotMem traceD085.log)
    (writeLog snapshotMem traceD085.log) traceD085.regs traceLds085_00 traceSeg085_00 := by
  have kind0 : (mkLine 0x80003fe0#64 0xf5010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003fe4#64 0xa813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80003fe8#64 0x8913c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003fec#64 0x9213823#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003ff0#64 0x9313423#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003ff4#64 0xa113423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80003ff8#64 0x58413#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003ffc#64 0x50493#32).kind = MKind.addi := by decide
  simp only [traceSeg085_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_08913c23
    | exact DecodeTable.decode_09213823
    | exact DecodeTable.decode_09313423
    | exact DecodeTable.decode_0a113423
    | exact DecodeTable.decode_0a813023
    | exact DecodeTable.decode_f5010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run085_00 {c : Config} (h : TraceHolds traceD085 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD085_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg085_00 traceLds085_00 (by decide) facts085_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run085_00

#derive_case traceSeg085_01 chain
  [(0x80004000#64, 0x60993#32),
   (0x80004004#64, 0x68913#32),
   (0x80004008#64, 0x800813#32),
   (0x8000400c#64, 0x16717#32),
   (0x80004010#64, 0xfac70713#32),
   (0x80004014#64, 0x42783#32)]
    terminator ⟨0x80004018#64, 0x06f86c63#32, 0x63#8, 0x6c#8, 0xf8#8, 0x06#8, .br bop.BLTU false, 16, 15, 0x0078#13, 0#21, 0#12⟩

def traceLds085_01 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts085_01 : ChainFacts (writeLog snapshotMem traceD085_01.log)
    (writeLog snapshotMem traceD085_01.log) traceD085_01.regs traceLds085_01 traceSeg085_01 := by
  have kind0 : (mkLine 0x80004000#64 0x60993#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80004004#64 0x68913#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004008#64 0x800813#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000400c#64 0x16717#32).kind = MKind.auipc := by decide
  have kind4 : (mkLine 0x80004010#64 0xfac70713#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80004014#64 0x42783#32).kind = MKind.lw := by decide
  simp only [traceSeg085_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00016717
    | exact DecodeTable.decode_00042783
    | exact DecodeTable.decode_00060993
    | exact DecodeTable.decode_00068913
    | exact DecodeTable.decode_00800813
    | exact DecodeTable.decode_06f86c63
    | exact DecodeTable.decode_fac70713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run085_01 {c : Config} (h : TraceHolds traceD085_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD085_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg085_01 traceLds085_01 (by decide) facts085_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run085_01

#derive_case traceSeg085_02 chain
  [(0x8000401c#64, 0x46783#32),
   (0x80004020#64, 0x279793#32),
   (0x80004024#64, 0xe787b3#32),
   (0x80004028#64, 0x7a783#32),
   (0x8000402c#64, 0xe787b3#32)]
    terminator ⟨0x80004030#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds085_02 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8],
   [0x30#8, 0xa2#8, 0xfe#8, 0xff#8]]

theorem facts085_02 : ChainFacts (writeLog snapshotMem traceD085_02.log)
    (writeLog snapshotMem traceD085_02.log) traceD085_02.regs traceLds085_02 traceSeg085_02 := by
  have kind0 : (mkLine 0x8000401c#64 0x46783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80004020#64 0x279793#32).kind = MKind.slli := by decide
  have kind2 : (mkLine 0x80004024#64 0xe787b3#32).kind = MKind.add := by decide
  have kind3 : (mkLine 0x80004028#64 0x7a783#32).kind = MKind.lw := by decide
  have kind4 : (mkLine 0x8000402c#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg085_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00046783
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00279793
    | exact DecodeTable.decode_00e787b3
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run085_02 {c : Config} (h : TraceHolds traceD085_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD086 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg085_02 traceLds085_02 (by decide) facts085_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run085_02
theorem run085 {c : Config} (h : TraceHolds traceD085 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD086 c' := by
  obtain ⟨c0, s0, h0⟩ := run085_00 h
  obtain ⟨c1, s1, h1⟩ := run085_01 h0
  obtain ⟨c2, s2, h2⟩ := run085_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run085
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg086 chain
  [(0x800041e8#64, 0x843603#32),
   (0x800041ec#64, 0x98693#32),
   (0x800041f0#64, 0x48593#32),
   (0x800041f4#64, 0x3810513#32)]

def traceLds086 : List (List (BitVec 8)) :=
  [[0xc0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts086 : ChainFacts (writeLog snapshotMem traceD086.log)
    (writeLog snapshotMem traceD086.log) traceD086.regs traceLds086 traceSeg086 := by
  have kind0 : (mkLine 0x800041e8#64 0x843603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800041ec#64 0x98693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800041f0#64 0x48593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800041f4#64 0x3810513#32).kind = MKind.addi := by decide
  simp only [traceSeg086, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048593
    | exact DecodeTable.decode_00098693
    | exact DecodeTable.decode_00843603
    | exact DecodeTable.decode_03810513
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run086 {c : Config} (h : TraceHolds traceD086 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD087 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg086 traceLds086 (by decide) facts086 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run086
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts087 : TraceCallFacts traceD087 0xf6dfe0ef#32
    (instruction.JAL (0x1fef6c#21, gprIdx 1)) 0xef#8 0xe0#8 0xdf#8 0xf6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_f6dfe0ef

theorem run087 {c : Config} (h : TraceHolds traceD087 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD088 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xf6dfe0ef#32 0x1fef6c#21 0xef#8 0xe0#8 0xdf#8 0xf6#8 facts087 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run087
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD088_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x800041fc#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000c0#64), (9, 0x87fffe10#64), (10, 0x87fffbd8#64), (11, 0x87fffe10#64), (12, 0x820000c0#64), (13, 0x81000000#64), (14, 0x6#64), (15, 0xa#64), (16, 0x8#64), (17, 0x8001bb97#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 114,
    out := #["\n"], payload := 0x0#4 }

def traceD088_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x800041fc#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000c0#64), (9, 0x87fffe10#64), (10, 0x87fffbd8#64), (11, 0x87fffe10#64), (12, 0x820000c0#64), (13, 0x81000000#64), (14, 0x6#64), (15, 0xa#64), (16, 0x8#64), (17, 0x8001bb97#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 114,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg088_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds088_00 : List (List (BitVec 8)) :=
  [[0x6#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts088_00 : ChainFacts (writeLog snapshotMem traceD088.log)
    (writeLog snapshotMem traceD088.log) traceD088.regs traceLds088_00 traceSeg088_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg088_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run088_00 {c : Config} (h : TraceHolds traceD088 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD088_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg088_00 traceLds088_00 (by decide) facts088_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run088_00

#derive_case traceSeg088_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds088_01 : List (List (BitVec 8)) :=
  []

theorem facts088_01 : ChainFacts (writeLog snapshotMem traceD088_01.log)
    (writeLog snapshotMem traceD088_01.log) traceD088_01.regs traceLds088_01 traceSeg088_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg088_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run088_01 {c : Config} (h : TraceHolds traceD088_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD088_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg088_01 traceLds088_01 (by decide) facts088_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run088_01

#derive_case traceSeg088_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds088_02 : List (List (BitVec 8)) :=
  [[0x6#8, 0x0#8, 0x0#8, 0x0#8],
   [0x90#8, 0x95#8, 0xfe#8, 0xff#8]]

theorem facts088_02 : ChainFacts (writeLog snapshotMem traceD088_02.log)
    (writeLog snapshotMem traceD088_02.log) traceD088_02.regs traceLds088_02 traceSeg088_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg088_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run088_02 {c : Config} (h : TraceHolds traceD088_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD089 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg088_02 traceLds088_02 (by decide) facts088_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run088_02
theorem run088 {c : Config} (h : TraceHolds traceD088 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD089 c' := by
  obtain ⟨c0, s0, h0⟩ := run088_00 h
  obtain ⟨c1, s1, h1⟩ := run088_01 h0
  obtain ⟨c2, s2, h2⟩ := run088_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run088
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg089 chain
  [(0x800034e8#64, 0x1063603#32),
   (0x800034ec#64, 0x7810513#32),
   (0x800034f0#64, 0x41313c23#32),
   (0x800034f4#64, 0xd13023#32)]

def traceLds089 : List (List (BitVec 8)) :=
  [[0x0#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts089 : ChainFacts (writeLog snapshotMem traceD089.log)
    (writeLog snapshotMem traceD089.log) traceD089.regs traceLds089 traceSeg089 := by
  have kind0 : (mkLine 0x800034e8#64 0x1063603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800034ec#64 0x7810513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800034f0#64 0x41313c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x800034f4#64 0xd13023#32).kind = MKind.sd := by decide
  simp only [traceSeg089, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00d13023
    | exact DecodeTable.decode_01063603
    | exact DecodeTable.decode_07810513
    | exact DecodeTable.decode_41313c23
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run089 {c : Config} (h : TraceHolds traceD089 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD090 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg089 traceLds089 (by decide) facts089 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run089
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts090 : TraceCallFacts traceD090 0xc6dff0ef#32
    (instruction.JAL (0x1ffc6c#21, gprIdx 1)) 0xef#8 0xf0#8 0xdf#8 0xc6#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_c6dff0ef

theorem run090 {c : Config} (h : TraceHolds traceD090 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD091 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc6dff0ef#32 0x1ffc6c#21 0xef#8 0xf0#8 0xdf#8 0xc6#8 facts090 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run090
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD091_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x800034fc#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000100#64), (9, 0x87fffbd8#64), (10, 0x87fff7d8#64), (11, 0x87fffe10#64), (12, 0x82000100#64), (13, 0x81000000#64), (14, 0x1#64), (15, 0xa#64), (16, 0x8#64), (17, 0x8001bb97#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 120,
    out := #["\n"], payload := 0x0#4 }

def traceD091_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x800034fc#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000100#64), (9, 0x87fffbd8#64), (10, 0x87fff7d8#64), (11, 0x87fffe10#64), (12, 0x82000100#64), (13, 0x81000000#64), (14, 0x1#64), (15, 0xa#64), (16, 0x8#64), (17, 0x8001bb97#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 120,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg091_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds091_00 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts091_00 : ChainFacts (writeLog snapshotMem traceD091.log)
    (writeLog snapshotMem traceD091.log) traceD091.regs traceLds091_00 traceSeg091_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg091_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run091_00 {c : Config} (h : TraceHolds traceD091 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD091_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg091_00 traceLds091_00 (by decide) facts091_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run091_00

#derive_case traceSeg091_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds091_01 : List (List (BitVec 8)) :=
  []

theorem facts091_01 : ChainFacts (writeLog snapshotMem traceD091_01.log)
    (writeLog snapshotMem traceD091_01.log) traceD091_01.regs traceLds091_01 traceSeg091_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg091_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run091_01 {c : Config} (h : TraceHolds traceD091_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD091_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg091_01 traceLds091_01 (by decide) facts091_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run091_01

#derive_case traceSeg091_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds091_02 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8],
   [0xbc#8, 0x94#8, 0xfe#8, 0xff#8]]

theorem facts091_02 : ChainFacts (writeLog snapshotMem traceD091_02.log)
    (writeLog snapshotMem traceD091_02.log) traceD091_02.regs traceLds091_02 traceSeg091_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg091_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run091_02 {c : Config} (h : TraceHolds traceD091_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD092 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg091_02 traceLds091_02 (by decide) facts091_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run091_02
theorem run091 {c : Config} (h : TraceHolds traceD091 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD092 c' := by
  obtain ⟨c0, s0, h0⟩ := run091_00 h
  obtain ⟨c1, s1, h1⟩ := run091_01 h0
  obtain ⟨c2, s2, h2⟩ := run091_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run091
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg092 chain
  [(0x80003414#64, 0x863583#32)]

def traceLds092 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts092 : ChainFacts (writeLog snapshotMem traceD092.log)
    (writeLog snapshotMem traceD092.log) traceD092.regs traceLds092 traceSeg092 := by
  have kind0 : (mkLine 0x80003414#64 0x863583#32).kind = MKind.ld := by decide
  simp only [traceSeg092, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00863583
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run092 {c : Config} (h : TraceHolds traceD092 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD093 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg092 traceLds092 (by decide) facts092 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run092
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts093 : TraceCallFacts traceD093 0xc04ff0ef#32
    (instruction.JAL (0x1ff404#21, gprIdx 1)) 0xef#8 0xf0#8 0x4f#8 0xc0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_c04ff0ef

theorem run093 {c : Config} (h : TraceHolds traceD093 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD094 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc04ff0ef#32 0x1ff404#21 0xef#8 0xf0#8 0x4f#8 0xc0#8 facts093 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run093
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg094 chain
  [(0x8000281c#64, 0x300793#32),
   (0x80002820#64, 0xb53423#32),
   (0x80002824#64, 0xf52023#32)]
    terminator ⟨0x80002828#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds094 : List (List (BitVec 8)) :=
  []

theorem facts094 : ChainFacts (writeLog snapshotMem traceD094.log)
    (writeLog snapshotMem traceD094.log) traceD094.regs traceLds094 traceSeg094 := by
  have kind0 : (mkLine 0x8000281c#64 0x300793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002820#64 0xb53423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002824#64 0xf52023#32).kind = MKind.sw := by decide
  simp only [traceSeg094, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run094 {c : Config} (h : TraceHolds traceD094 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD095 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg094 traceLds094 (by decide) facts094 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run094
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg095 chain
  []
    terminator ⟨0x8000341c#64, 0xfd1ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xfd#8, .j, 0, 0, 0#13, 0x1fffd0#21, 0#12⟩ ;;
  [(0x800033ec#64, 0x43813083#32),
   (0x800033f0#64, 0x43013403#32),
   (0x800033f4#64, 0x42013903#32),
   (0x800033f8#64, 0x48513#32),
   (0x800033fc#64, 0x42813483#32),
   (0x80003400#64, 0x44010113#32)]
    terminator ⟨0x80003404#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds095 : List (List (BitVec 8)) :=
  [[0xfc#8, 0x34#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts095 : ChainFacts (writeLog snapshotMem traceD095.log)
    (writeLog snapshotMem traceD095.log) traceD095.regs traceLds095 traceSeg095 := by
  have kind0 : (mkLine 0x800033ec#64 0x43813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800033f0#64 0x43013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800033f4#64 0x42013903#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800033f8#64 0x48513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x800033fc#64 0x42813483#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80003400#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg095, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run095 {c : Config} (h : TraceHolds traceD095 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD096 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg095 traceLds095 (by decide) facts095 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run095
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg096 chain
  [(0x800034fc#64, 0x1843603#32),
   (0x80003500#64, 0x13683#32),
   (0x80003504#64, 0x7812803#32),
   (0x80003508#64, 0x9010513#32),
   (0x8000350c#64, 0x90593#32),
   (0x80003510#64, 0x8013983#32),
   (0x80003514#64, 0x1013023#32)]

def traceLds096 : List (List (BitVec 8)) :=
  [[0x20#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8],
   [0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts096 : ChainFacts (writeLog snapshotMem traceD096.log)
    (writeLog snapshotMem traceD096.log) traceD096.regs traceLds096 traceSeg096 := by
  have kind0 : (mkLine 0x800034fc#64 0x1843603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80003500#64 0x13683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80003504#64 0x7812803#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x80003508#64 0x9010513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000350c#64 0x90593#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80003510#64 0x8013983#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80003514#64 0x1013023#32).kind = MKind.sd := by decide
  simp only [traceSeg096, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013683
    | exact DecodeTable.decode_00090593
    | exact DecodeTable.decode_01013023
    | exact DecodeTable.decode_01843603
    | exact DecodeTable.decode_07812803
    | exact DecodeTable.decode_08013983
    | exact DecodeTable.decode_09010513
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run096 {c : Config} (h : TraceHolds traceD096 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD097 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg096 traceLds096 (by decide) facts096 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 122 ++ (evalBlocks traceSeg096 (SegEvalState.init traceD096.regs traceLds096)).log = traceStores.take 123
  have hw : (evalBlocks traceSeg096 (SegEvalState.init traceD096.regs traceLds096)).log = (traceStores.drop 122).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run096
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts097 : TraceCallFacts traceD097 0xc4dff0ef#32
    (instruction.JAL (0x1ffc4c#21, gprIdx 1)) 0xef#8 0xf0#8 0xdf#8 0xc4#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_c4dff0ef

theorem run097 {c : Config} (h : TraceHolds traceD097 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD098 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc4dff0ef#32 0x1ffc4c#21 0xef#8 0xf0#8 0xdf#8 0xc4#8 facts097 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run097
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD098_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x8000351c#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000120#64), (9, 0x87fffbd8#64), (10, 0x87fff7f0#64), (11, 0x87fffe10#64), (12, 0x82000120#64), (13, 0x81000000#64), (14, 0x1#64), (15, 0xa#64), (16, 0x3#64), (17, 0x8001bb97#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 127,
    out := #["\n"], payload := 0x0#4 }

def traceD098_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x8000351c#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000120#64), (9, 0x87fffbd8#64), (10, 0x87fff7f0#64), (11, 0x87fffe10#64), (12, 0x82000120#64), (13, 0x81000000#64), (14, 0x1#64), (15, 0xa#64), (16, 0x3#64), (17, 0x8001bb97#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 127,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg098_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds098_00 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts098_00 : ChainFacts (writeLog snapshotMem traceD098.log)
    (writeLog snapshotMem traceD098.log) traceD098.regs traceLds098_00 traceSeg098_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg098_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run098_00 {c : Config} (h : TraceHolds traceD098 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD098_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg098_00 traceLds098_00 (by decide) facts098_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 123 ++ (evalBlocks traceSeg098_00 (SegEvalState.init traceD098.regs traceLds098_00)).log = traceStores.take 127
  have hw : (evalBlocks traceSeg098_00 (SegEvalState.init traceD098.regs traceLds098_00)).log = (traceStores.drop 123).take 4 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run098_00

#derive_case traceSeg098_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds098_01 : List (List (BitVec 8)) :=
  []

theorem facts098_01 : ChainFacts (writeLog snapshotMem traceD098_01.log)
    (writeLog snapshotMem traceD098_01.log) traceD098_01.regs traceLds098_01 traceSeg098_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg098_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run098_01 {c : Config} (h : TraceHolds traceD098_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD098_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg098_01 traceLds098_01 (by decide) facts098_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 127 ++ (evalBlocks traceSeg098_01 (SegEvalState.init traceD098_01.regs traceLds098_01)).log = traceStores.take 127
  have hw : (evalBlocks traceSeg098_01 (SegEvalState.init traceD098_01.regs traceLds098_01)).log = (traceStores.drop 127).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run098_01

#derive_case traceSeg098_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds098_02 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8],
   [0xbc#8, 0x94#8, 0xfe#8, 0xff#8]]

theorem facts098_02 : ChainFacts (writeLog snapshotMem traceD098_02.log)
    (writeLog snapshotMem traceD098_02.log) traceD098_02.regs traceLds098_02 traceSeg098_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg098_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run098_02 {c : Config} (h : TraceHolds traceD098_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD099 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg098_02 traceLds098_02 (by decide) facts098_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 127 ++ (evalBlocks traceSeg098_02 (SegEvalState.init traceD098_02.regs traceLds098_02)).log = traceStores.take 127
  have hw : (evalBlocks traceSeg098_02 (SegEvalState.init traceD098_02.regs traceLds098_02)).log = (traceStores.drop 127).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run098_02
theorem run098 {c : Config} (h : TraceHolds traceD098 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD099 c' := by
  obtain ⟨c0, s0, h0⟩ := run098_00 h
  obtain ⟨c1, s1, h1⟩ := run098_01 h0
  obtain ⟨c2, s2, h2⟩ := run098_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run098
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg099 chain
  [(0x80003414#64, 0x863583#32)]

def traceLds099 : List (List (BitVec 8)) :=
  [[0x40#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts099 : ChainFacts (writeLog snapshotMem traceD099.log)
    (writeLog snapshotMem traceD099.log) traceD099.regs traceLds099 traceSeg099 := by
  have kind0 : (mkLine 0x80003414#64 0x863583#32).kind = MKind.ld := by decide
  simp only [traceSeg099, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00863583
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run099 {c : Config} (h : TraceHolds traceD099 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD100 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg099 traceLds099 (by decide) facts099 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 127 ++ (evalBlocks traceSeg099 (SegEvalState.init traceD099.regs traceLds099)).log = traceStores.take 127
  have hw : (evalBlocks traceSeg099 (SegEvalState.init traceD099.regs traceLds099)).log = (traceStores.drop 127).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run099
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts100 : TraceCallFacts traceD100 0xc04ff0ef#32
    (instruction.JAL (0x1ff404#21, gprIdx 1)) 0xef#8 0xf0#8 0x4f#8 0xc0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_c04ff0ef

theorem run100 {c : Config} (h : TraceHolds traceD100 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD101 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc04ff0ef#32 0x1ff404#21 0xef#8 0xf0#8 0x4f#8 0xc0#8 facts100 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run100
end Vsa.Sim.OutputAliasLoaded
