import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part28
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part23
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part28
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part32
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part05
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part12
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part14
import Vsa.Sim.DecodeTable.Batch09Part20
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part08
import Vsa.Sim.DecodeTable.Batch13Part11
import Vsa.Sim.DecodeTable.Batch13Part13
import Vsa.Sim.DecodeTable.Batch13Part22
import Vsa.Sim.DecodeTable.Batch13Part25
import Vsa.Sim.DecodeTable.Batch15Part18
import Vsa.Sim.DecodeTable.Batch15Part26
import Vsa.Sim.DecodeTable.Batch16Part02
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg061 chain
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

def traceLds061 : List (List (BitVec 8)) :=
  [[0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts061 : ChainFacts (writeLog snapshotMem traceD061.log)
    (writeLog snapshotMem traceD061.log) traceD061.regs traceLds061 traceSeg061 := by
  have kind0 : (mkLine 0x8000ee10#64 0x13583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee14#64 0x50793#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ee18#64 0xb05a703#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000ee1c#64 0x177713#32).kind = MKind.andi := by decide
  have kind4 : (mkLine 0x8000ee24#64 0x105d703#32).kind = MKind.lhu := by decide
  have kind5 : (mkLine 0x8000ee28#64 0x20077713#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000ee5c#64 0xa13023#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x8000ee60#64 0xa05b503#32).kind = MKind.ld := by decide
  simp only [traceSeg061, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run061 {c : Config} (h : TraceHolds traceD061 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD062 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg061 traceLds061 (by decide) facts061 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run061
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts062 : TraceCallFacts traceD062 0x994f80ef#32
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

theorem run062 {c : Config} (h : TraceHolds traceD062 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD063 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x994f80ef#32 0x1f8194#21 0xef#8 0x80#8 0x4f#8 0x99#8 facts062 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run062
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg063 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds063 : List (List (BitVec 8)) :=
  []

theorem facts063 : ChainFacts (writeLog snapshotMem traceD063.log)
    (writeLog snapshotMem traceD063.log) traceD063.regs traceLds063 traceSeg063 := by
  simp only [traceSeg063, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run063 {c : Config} (h : TraceHolds traceD063 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD064 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg063 traceLds063 (by decide) facts063 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run063
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg064 chain
  [(0x8000ee68#64, 0x13783#32),
   (0x8000ee6c#64, 0x1813083#32),
   (0x8000ee70#64, 0x78513#32),
   (0x8000ee74#64, 0x2010113#32)]
    terminator ⟨0x8000ee78#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds064 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xdc#8, 0xf1#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts064 : ChainFacts (writeLog snapshotMem traceD064.log)
    (writeLog snapshotMem traceD064.log) traceD064.regs traceLds064 traceSeg064 := by
  have kind0 : (mkLine 0x8000ee68#64 0x13783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee6c#64 0x1813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ee70#64 0x78513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ee74#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg064, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run064 {c : Config} (h : TraceHolds traceD064 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD065 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg064 traceLds064 (by decide) facts064 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run064
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg065 chain
  []
    terminator ⟨0x8000f1dc#64, 0xf8050ae3#32, 0xe3#8, 0x0a#8, 0x05#8, 0xf8#8, .br bop.BEQ true, 10, 0, 0x1f94#13, 0#21, 0#12⟩ ;;
  [(0x8000f170#64, 0x2813083#32),
   (0x8000f174#64, 0x40513#32),
   (0x8000f178#64, 0x2013403#32),
   (0x8000f17c#64, 0x1813483#32),
   (0x8000f180#64, 0x3010113#32)]
    terminator ⟨0x8000f184#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds065 : List (List (BitVec 8)) :=
  [[0x40#8, 0xe7#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts065 : ChainFacts (writeLog snapshotMem traceD065.log)
    (writeLog snapshotMem traceD065.log) traceD065.regs traceLds065 traceSeg065 := by
  have kind0 : (mkLine 0x8000f170#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000f174#64 0x40513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000f178#64 0x2013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000f17c#64 0x1813483#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x8000f180#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg065, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run065 {c : Config} (h : TraceHolds traceD065 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD066 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg065 traceLds065 (by decide) facts065 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run065
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg066 chain
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

def traceLds066 : List (List (BitVec 8)) :=
  [[0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts066 : ChainFacts (writeLog snapshotMem traceD066.log)
    (writeLog snapshotMem traceD066.log) traceD066.regs traceLds066 traceSeg066 := by
  have kind0 : (mkLine 0x8000e740#64 0x813603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e744#64 0x50593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000e70c#64 0xb062783#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000e710#64 0x17f793#32).kind = MKind.andi := by decide
  have kind4 : (mkLine 0x8000e718#64 0x1065783#32).kind = MKind.lhu := by decide
  have kind5 : (mkLine 0x8000e71c#64 0x2007f793#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000e770#64 0xa063503#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x8000e774#64 0xb13423#32).kind = MKind.sd := by decide
  simp only [traceSeg066, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run066 {c : Config} (h : TraceHolds traceD066 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD067 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg066 traceLds066 (by decide) facts066 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run066
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts067 : TraceCallFacts traceD067 0x881f80ef#32
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

theorem run067 {c : Config} (h : TraceHolds traceD067 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD068 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x881f80ef#32 0x1f8880#21 0xef#8 0x80#8 0x1f#8 0x88#8 facts067 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run067
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg068 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds068 : List (List (BitVec 8)) :=
  []

theorem facts068 : ChainFacts (writeLog snapshotMem traceD068.log)
    (writeLog snapshotMem traceD068.log) traceD068.regs traceLds068 traceSeg068 := by
  simp only [traceSeg068, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run068 {c : Config} (h : TraceHolds traceD068 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD069 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg068 traceLds068 (by decide) facts068 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run068
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg069 chain
  [(0x8000e77c#64, 0x813583#32),
   (0x8000e780#64, 0x2813083#32),
   (0x8000e784#64, 0x58513#32),
   (0x8000e788#64, 0x3010113#32)]
    terminator ⟨0x8000e78c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds069 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x2c#8, 0x63#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts069 : ChainFacts (writeLog snapshotMem traceD069.log)
    (writeLog snapshotMem traceD069.log) traceD069.regs traceLds069 traceSeg069 := by
  have kind0 : (mkLine 0x8000e77c#64 0x813583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e780#64 0x2813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e784#64 0x58513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000e788#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg069, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00058513
    | exact DecodeTable.decode_00813583
    | exact DecodeTable.decode_02813083
    | exact DecodeTable.decode_03010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run069 {c : Config} (h : TraceHolds traceD069 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD070 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg069 traceLds069 (by decide) facts069 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run069
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg070 chain
  [(0x8000632c#64, 0xb042783#32),
   (0x80006330#64, 0x50713#32),
   (0x80006334#64, 0x17f793#32)]
    terminator ⟨0x80006338#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000633c#64, 0x1045783#32),
   (0x80006340#64, 0x2007f793#32)]
    terminator ⟨0x80006344#64, 0x00078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x8000635c#64, 0xa13023#32),
   (0x80006360#64, 0xa043503#32)]

def traceLds070 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts070 : ChainFacts (writeLog snapshotMem traceD070.log)
    (writeLog snapshotMem traceD070.log) traceD070.regs traceLds070 traceSeg070 := by
  have kind0 : (mkLine 0x8000632c#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80006330#64 0x50713#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006334#64 0x17f793#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000633c#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind4 : (mkLine 0x80006340#64 0x2007f793#32).kind = MKind.andi := by decide
  have kind5 : (mkLine 0x8000635c#64 0xa13023#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80006360#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg070, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050713
    | exact DecodeTable.decode_00078c63
    | exact DecodeTable.decode_00079863
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_00a13023
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_0a043503
    | exact DecodeTable.decode_0b042783
    | exact DecodeTable.decode_2007f793
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run070 {c : Config} (h : TraceHolds traceD070 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD071 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg070 traceLds070 (by decide) facts070 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run070
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts071 : TraceCallFacts traceD071 0x495000ef#32
    (instruction.JAL (0xc94#21, gprIdx 1)) 0xef#8 0x0#8 0x50#8 0x49#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_495000ef

theorem run071 {c : Config} (h : TraceHolds traceD071 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD072 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x495000ef#32 0xc94#21 0xef#8 0x0#8 0x50#8 0x49#8 facts071 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run071
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg072 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds072 : List (List (BitVec 8)) :=
  []

theorem facts072 : ChainFacts (writeLog snapshotMem traceD072.log)
    (writeLog snapshotMem traceD072.log) traceD072.regs traceLds072 traceSeg072 := by
  simp only [traceSeg072, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run072 {c : Config} (h : TraceHolds traceD072 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD073 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg072 traceLds072 (by decide) facts072 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run072
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg073 chain
  [(0x80006368#64, 0x13703#32),
   (0x8000636c#64, 0x1813083#32),
   (0x80006370#64, 0x1013403#32),
   (0x80006374#64, 0x70513#32),
   (0x80006378#64, 0x2010113#32)]
    terminator ⟨0x8000637c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds073 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa4#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts073 : ChainFacts (writeLog snapshotMem traceD073.log)
    (writeLog snapshotMem traceD073.log) traceD073.regs traceLds073 traceSeg073 := by
  have kind0 : (mkLine 0x80006368#64 0x13703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000636c#64 0x1813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80006370#64 0x1013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80006374#64 0x70513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80006378#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg073, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00013703
    | exact DecodeTable.decode_00070513
    | exact DecodeTable.decode_01013403
    | exact DecodeTable.decode_01813083
    | exact DecodeTable.decode_02010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run073 {c : Config} (h : TraceHolds traceD073 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD074 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg073 traceLds073 (by decide) facts073 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run073
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg074 chain
  [(0x80002fa4#64, 0x40513#32)]

def traceLds074 : List (List (BitVec 8)) :=
  []

theorem facts074 : ChainFacts (writeLog snapshotMem traceD074.log)
    (writeLog snapshotMem traceD074.log) traceD074.regs traceLds074 traceSeg074 := by
  have kind0 : (mkLine 0x80002fa4#64 0x40513#32).kind = MKind.addi := by decide
  simp only [traceSeg074, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00040513
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run074 {c : Config} (h : TraceHolds traceD074 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD075 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg074 traceLds074 (by decide) facts074 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run074
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts075 : TraceCallFacts traceD075 0x845ff0ef#32
    (instruction.JAL (0x1ff844#21, gprIdx 1)) 0xef#8 0xf0#8 0x5f#8 0x84#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_845ff0ef

theorem run075 {c : Config} (h : TraceHolds traceD075 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD076 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x845ff0ef#32 0x1ff844#21 0xef#8 0xf0#8 0x5f#8 0x84#8 facts075 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run075
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg076 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds076 : List (List (BitVec 8)) :=
  []

theorem facts076 : ChainFacts (writeLog snapshotMem traceD076.log)
    (writeLog snapshotMem traceD076.log) traceD076.regs traceLds076 traceSeg076 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg076, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run076 {c : Config} (h : TraceHolds traceD076 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD077 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg076 traceLds076 (by decide) facts076 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run076
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg077 chain
  [(0x80002fac#64, 0x2813083#32),
   (0x80002fb0#64, 0x40513#32),
   (0x80002fb4#64, 0x2013403#32),
   (0x80002fb8#64, 0x3010113#32)]
    terminator ⟨0x80002fbc#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds077 : List (List (BitVec 8)) :=
  [[0xf8#8, 0x39#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts077 : ChainFacts (writeLog snapshotMem traceD077.log)
    (writeLog snapshotMem traceD077.log) traceD077.regs traceLds077 traceSeg077 := by
  have kind0 : (mkLine 0x80002fac#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002fb0#64 0x40513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002fb4#64 0x2013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002fb8#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg077, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00040513
    | exact DecodeTable.decode_02013403
    | exact DecodeTable.decode_02813083
    | exact DecodeTable.decode_03010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run077 {c : Config} (h : TraceHolds traceD077 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD078 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg077 traceLds077 (by decide) facts077 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run077
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg078 chain
  [(0x800039f8#64, 0x3f813b83#32)]
    terminator ⟨0x800039fc#64, 0x9f1ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0x9f#8, .j, 0, 0, 0#13, 0x1ff9f0#21, 0#12⟩ ;;
  [(0x800033ec#64, 0x43813083#32),
   (0x800033f0#64, 0x43013403#32),
   (0x800033f4#64, 0x42013903#32),
   (0x800033f8#64, 0x48513#32),
   (0x800033fc#64, 0x42813483#32),
   (0x80003400#64, 0x44010113#32)]
    terminator ⟨0x80003404#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds078 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x84#8, 0x41#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa8#8, 0xfc#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts078 : ChainFacts (writeLog snapshotMem traceD078.log)
    (writeLog snapshotMem traceD078.log) traceD078.regs traceLds078 traceSeg078 := by
  have kind0 : (mkLine 0x800039f8#64 0x3f813b83#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800033ec#64 0x43813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800033f0#64 0x43013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800033f4#64 0x42013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800033f8#64 0x48513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800033fc#64 0x42813483#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80003400#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg078, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_3f813b83
    | exact DecodeTable.decode_42013903
    | exact DecodeTable.decode_42813483
    | exact DecodeTable.decode_43013403
    | exact DecodeTable.decode_43813083
    | exact DecodeTable.decode_44010113
    | exact DecodeTable.decode_9f1ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run078 {c : Config} (h : TraceHolds traceD078 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD079 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg078 traceLds078 (by decide) facts078 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run078
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg079 chain
  [(0x80004184#64, 0x513#32)]
    terminator ⟨0x80004188#64, 0xf15ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf1#8, .j, 0, 0, 0#13, 0x1fff14#21, 0#12⟩ ;;
  [(0x8000409c#64, 0xa813083#32),
   (0x800040a0#64, 0xa013403#32),
   (0x800040a4#64, 0x9813483#32),
   (0x800040a8#64, 0x9013903#32),
   (0x800040ac#64, 0x8813983#32),
   (0x800040b0#64, 0xb010113#32)]
    terminator ⟨0x800040b4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds079 : List (List (BitVec 8)) :=
  [[0x78#8, 0x44#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts079 : ChainFacts (writeLog snapshotMem traceD079.log)
    (writeLog snapshotMem traceD079.log) traceD079.regs traceLds079 traceSeg079 := by
  have kind0 : (mkLine 0x80004184#64 0x513#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000409c#64 0xa813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800040a0#64 0xa013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800040a4#64 0x9813483#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800040a8#64 0x9013903#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x800040ac#64 0x8813983#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x800040b0#64 0xb010113#32).kind = MKind.addi := by decide
  simp only [traceSeg079, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_08813983
    | exact DecodeTable.decode_09013903
    | exact DecodeTable.decode_09813483
    | exact DecodeTable.decode_0a013403
    | exact DecodeTable.decode_0a813083
    | exact DecodeTable.decode_0b010113
    | exact DecodeTable.decode_f15ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run079 {c : Config} (h : TraceHolds traceD079 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD080 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg079 traceLds079 (by decide) facts079 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run079
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg080 chain
  []
    terminator ⟨0x80004478#64, 0x0d350463#32, 0x63#8, 0x04#8, 0x35#8, 0x0d#8, .br bop.BEQ false, 10, 19, 0x00c8#13, 0#21, 0#12⟩ ;;
  [(0x8000447c#64, 0xfff5051b#32)]
    terminator ⟨0x80004480#64, 0x0eaa7263#32, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8, .br bop.BGEU false, 20, 10, 0x00e4#13, 0#21, 0#12⟩ ;;
  [(0x80004484#64, 0x840413#32)]
    terminator ⟨0x80004488#64, 0x09240663#32, 0x63#8, 0x06#8, 0x24#8, 0x09#8, .br bop.BEQ false, 8, 18, 0x008c#13, 0#21, 0#12⟩ ;;
  [(0x8000448c#64, 0x813783#32),
   (0x80004490#64, 0x43483#32)]
    terminator ⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, .br bop.BEQ true, 15, 0, 0x1fc4#13, 0#21, 0#12⟩ ;;
  [(0x80004458#64, 0x5810513#32)]

def traceLds080 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x40#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts080 : ChainFacts (writeLog snapshotMem traceD080.log)
    (writeLog snapshotMem traceD080.log) traceD080.regs traceLds080 traceSeg080 := by
  have kind0 : (mkLine 0x8000447c#64 0xfff5051b#32).kind = MKind.addiw := by decide
  have kind1 : (mkLine 0x80004484#64 0x840413#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000448c#64 0x813783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80004490#64 0x43483#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004458#64 0x5810513#32).kind = MKind.addi := by decide
  simp only [traceSeg080, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00043483
    | exact DecodeTable.decode_00813783
    | exact DecodeTable.decode_00840413
    | exact DecodeTable.decode_05810513
    | exact DecodeTable.decode_09240663
    | exact DecodeTable.decode_0d350463
    | exact DecodeTable.decode_0eaa7263
    | exact DecodeTable.decode_fc0782e3
    | exact DecodeTable.decode_fff5051b
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run080 {c : Config} (h : TraceHolds traceD080 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD081 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg080 traceLds080 (by decide) facts080 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run080
end Vsa.Sim.OutputAliasLoaded
