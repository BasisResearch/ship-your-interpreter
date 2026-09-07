import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
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
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch02Part06
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part05
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part26
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part09
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part27
import Vsa.Sim.DecodeTable.Batch05Part29
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch07Part12
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part15
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch08Part25
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part23
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch10Part24
import Vsa.Sim.DecodeTable.Batch11Part14
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part05
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.DecodeTable.Batch14Part08
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch16Part02
import Vsa.Sim.DecodeTable.Batch16Part05
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

theorem facts001 : TraceCallFacts traceD001 0x3d9020ef#32
    (instruction.JAL (0x2bd8#21, gprIdx 1)) 0xef#8 0x20#8 0x90#8 0x3d#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_3d9020ef

theorem run001 {c : Config} (h : TraceHolds traceD001 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD002 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x3d9020ef#32 0x2bd8#21 0xef#8 0x20#8 0x90#8 0x3d#8 facts001 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run001
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg002 chain
  [(0x80006ffc#64, 0x153023#32),
   (0x80007000#64, 0x853423#32),
   (0x80007004#64, 0x953823#32),
   (0x80007008#64, 0x1253c23#32),
   (0x8000700c#64, 0x3353023#32),
   (0x80007010#64, 0x3453423#32),
   (0x80007014#64, 0x3553823#32),
   (0x80007018#64, 0x3653c23#32),
   (0x8000701c#64, 0x5753023#32),
   (0x80007020#64, 0x5853423#32),
   (0x80007024#64, 0x5953823#32),
   (0x80007028#64, 0x5a53c23#32),
   (0x8000702c#64, 0x7b53023#32),
   (0x80007030#64, 0x6253423#32),
   (0x80007034#64, 0x513#32)]
    terminator ⟨0x80007038#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds002 : List (List (BitVec 8)) :=
  []

theorem facts002 : ChainFacts (writeLog snapshotMem traceD002.log)
    (writeLog snapshotMem traceD002.log) traceD002.regs traceLds002 traceSeg002 := by
  have kind0 : (mkLine 0x80006ffc#64 0x153023#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x80007000#64 0x853423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80007004#64 0x953823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80007008#64 0x1253c23#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000700c#64 0x3353023#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80007010#64 0x3453423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80007014#64 0x3553823#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80007018#64 0x3653c23#32).kind = MKind.sd := by decide
  have kind8 : (mkLine 0x8000701c#64 0x5753023#32).kind = MKind.sd := by decide
  have kind9 : (mkLine 0x80007020#64 0x5853423#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x80007024#64 0x5953823#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x80007028#64 0x5a53c23#32).kind = MKind.sd := by decide
  have kind12 : (mkLine 0x8000702c#64 0x7b53023#32).kind = MKind.sd := by decide
  have kind13 : (mkLine 0x80007030#64 0x6253423#32).kind = MKind.sd := by decide
  have kind14 : (mkLine 0x80007034#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg002, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00153023
    | exact DecodeTable.decode_00853423
    | exact DecodeTable.decode_00953823
    | exact DecodeTable.decode_01253c23
    | exact DecodeTable.decode_03353023
    | exact DecodeTable.decode_03453423
    | exact DecodeTable.decode_03553823
    | exact DecodeTable.decode_03653c23
    | exact DecodeTable.decode_05753023
    | exact DecodeTable.decode_05853423
    | exact DecodeTable.decode_05953823
    | exact DecodeTable.decode_05a53c23
    | exact DecodeTable.decode_06253423
    | exact DecodeTable.decode_07b53023
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, kind13, kind14, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run002 {c : Config} (h : TraceHolds traceD002 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD003 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg002 traceLds002 (by decide) facts002 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run002
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg003 chain
  []
    terminator ⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8, .br bop.BNE false, 10, 0, 0x00e0#13, 0#21, 0#12⟩ ;;
  [(0x8000442c#64, 0x1013783#32),
   (0x80004430#64, 0x50a93#32)]
    terminator ⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8, .br bop.BGE false, 0, 15, 0x00e0#13, 0#21, 0#12⟩ ;;
  [(0x80004438#64, 0x1013783#32),
   (0x8000443c#64, 0x1813403#32),
   (0x80004440#64, 0x46018b13#32),
   (0x80004444#64, 0x379913#32),
   (0x80004448#64, 0x1240933#32),
   (0x8000444c#64, 0x300993#32),
   (0x80004450#64, 0x100a13#32)]
    terminator ⟨0x80004454#64, 0x0380006f#32, 0x6f#8, 0x00#8, 0x80#8, 0x03#8, .j, 0, 0, 0#13, 0x000038#21, 0#12⟩ ;;
  [(0x8000448c#64, 0x813783#32),
   (0x80004490#64, 0x43483#32)]
    terminator ⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, .br bop.BEQ true, 15, 0, 0x1fc4#13, 0#21, 0#12⟩ ;;
  [(0x80004458#64, 0x5810513#32)]

def traceLds003 : List (List (BitVec 8)) :=
  [[0x2#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x2#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts003 : ChainFacts (writeLog snapshotMem traceD003.log)
    (writeLog snapshotMem traceD003.log) traceD003.regs traceLds003 traceSeg003 := by
  have kind0 : (mkLine 0x8000442c#64 0x1013783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004430#64 0x50a93#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004438#64 0x1013783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000443c#64 0x1813403#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004440#64 0x46018b13#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80004444#64 0x379913#32).kind = MKind.slli := by decide
  have kind6 : (mkLine 0x80004448#64 0x1240933#32).kind = MKind.add := by decide
  have kind7 : (mkLine 0x8000444c#64 0x300993#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x80004450#64 0x100a13#32).kind = MKind.addi := by decide
  have kind9 : (mkLine 0x8000448c#64 0x813783#32).kind = MKind.ld := by decide
  have kind10 : (mkLine 0x80004490#64 0x43483#32).kind = MKind.ld := by decide
  have kind11 : (mkLine 0x80004458#64 0x5810513#32).kind = MKind.addi := by decide
  simp only [traceSeg003, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00043483
    | exact DecodeTable.decode_00050a93
    | exact DecodeTable.decode_00100a13
    | exact DecodeTable.decode_00300993
    | exact DecodeTable.decode_00379913
    | exact DecodeTable.decode_00813783
    | exact DecodeTable.decode_01013783
    | exact DecodeTable.decode_01240933
    | exact DecodeTable.decode_01813403
    | exact DecodeTable.decode_0380006f
    | exact DecodeTable.decode_05810513
    | exact DecodeTable.decode_0e051063
    | exact DecodeTable.decode_0ef05063
    | exact DecodeTable.decode_46018b13
    | exact DecodeTable.decode_fc0782e3
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run003 {c : Config} (h : TraceHolds traceD003 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD004 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg003 traceLds003 (by decide) facts003 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run003
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts004 : TraceCallFacts traceD004 0xb90fe0ef#32
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

theorem run004 {c : Config} (h : TraceHolds traceD004 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD005 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb90fe0ef#32 0x1fe390#21 0xef#8 0xe0#8 0xf#8 0xb9#8 facts004 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run004
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg005 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds005 : List (List (BitVec 8)) :=
  []

theorem facts005 : ChainFacts (writeLog snapshotMem traceD005.log)
    (writeLog snapshotMem traceD005.log) traceD005.regs traceLds005 traceSeg005 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg005, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run005 {c : Config} (h : TraceHolds traceD005 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD006 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg005 traceLds005 (by decide) facts005 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run005
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg006 chain
  [(0x80004460#64, 0x13783#32),
   (0x80004464#64, 0x5810693#32),
   (0x80004468#64, 0x48593#32),
   (0x8000446c#64, 0x7b603#32),
   (0x80004470#64, 0x78513#32)]

def traceLds006 : List (List (BitVec 8)) :=
  [[0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts006 : ChainFacts (writeLog snapshotMem traceD006.log)
    (writeLog snapshotMem traceD006.log) traceD006.regs traceLds006 traceSeg006 := by
  have kind0 : (mkLine 0x80004460#64 0x13783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004464#64 0x5810693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004468#64 0x48593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000446c#64 0x7b603#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004470#64 0x78513#32).kind = MKind.addi := by decide
  simp only [traceSeg006, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run006 {c : Config} (h : TraceHolds traceD006 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD007 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg006 traceLds006 (by decide) facts006 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run006
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts007 : TraceCallFacts traceD007 0xb6dff0ef#32
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

theorem run007 {c : Config} (h : TraceHolds traceD007 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD008 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb6dff0ef#32 0x1ffb6c#21 0xef#8 0xf0#8 0xdf#8 0xb6#8 facts007 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run007
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD008_01 : TraceData :=
  { pc := 0x80004000#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffba0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000020#64), (9, 0x87fffe10#64), (10, 0x87fffe10#64), (11, 0x82000020#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x0#64), (15, 0x87fffe10#64), (16, 0x0#64), (17, 0x0#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 33,
    out := #[], payload := 0x0#4 }

def traceD008_02 : TraceData :=
  { pc := 0x8000401c#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffba0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000020#64), (9, 0x87fffe10#64), (10, 0x87fffe10#64), (11, 0x82000020#64), (12, 0x81000000#64), (13, 0x87fffca8#64), (14, 0x80019fb8#64), (15, 0x0#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 33,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg008_00 chain
  [(0x80003fe0#64, 0xf5010113#32),
   (0x80003fe4#64, 0xa813023#32),
   (0x80003fe8#64, 0x8913c23#32),
   (0x80003fec#64, 0x9213823#32),
   (0x80003ff0#64, 0x9313423#32),
   (0x80003ff4#64, 0xa113423#32),
   (0x80003ff8#64, 0x58413#32),
   (0x80003ffc#64, 0x50493#32)]

def traceLds008_00 : List (List (BitVec 8)) :=
  []

theorem facts008_00 : ChainFacts (writeLog snapshotMem traceD008.log)
    (writeLog snapshotMem traceD008.log) traceD008.regs traceLds008_00 traceSeg008_00 := by
  have kind0 : (mkLine 0x80003fe0#64 0xf5010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003fe4#64 0xa813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80003fe8#64 0x8913c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003fec#64 0x9213823#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003ff0#64 0x9313423#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003ff4#64 0xa113423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80003ff8#64 0x58413#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003ffc#64 0x50493#32).kind = MKind.addi := by decide
  simp only [traceSeg008_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run008_00 {c : Config} (h : TraceHolds traceD008 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD008_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg008_00 traceLds008_00 (by decide) facts008_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run008_00

#derive_case traceSeg008_01 chain
  [(0x80004000#64, 0x60993#32),
   (0x80004004#64, 0x68913#32),
   (0x80004008#64, 0x800813#32),
   (0x8000400c#64, 0x16717#32),
   (0x80004010#64, 0xfac70713#32),
   (0x80004014#64, 0x42783#32)]
    terminator ⟨0x80004018#64, 0x06f86c63#32, 0x63#8, 0x6c#8, 0xf8#8, 0x06#8, .br bop.BLTU false, 16, 15, 0x0078#13, 0#21, 0#12⟩

def traceLds008_01 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts008_01 : ChainFacts (writeLog snapshotMem traceD008_01.log)
    (writeLog snapshotMem traceD008_01.log) traceD008_01.regs traceLds008_01 traceSeg008_01 := by
  have kind0 : (mkLine 0x80004000#64 0x60993#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80004004#64 0x68913#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004008#64 0x800813#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000400c#64 0x16717#32).kind = MKind.auipc := by decide
  have kind4 : (mkLine 0x80004010#64 0xfac70713#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80004014#64 0x42783#32).kind = MKind.lw := by decide
  simp only [traceSeg008_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run008_01 {c : Config} (h : TraceHolds traceD008_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD008_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg008_01 traceLds008_01 (by decide) facts008_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run008_01

#derive_case traceSeg008_02 chain
  [(0x8000401c#64, 0x46783#32),
   (0x80004020#64, 0x279793#32),
   (0x80004024#64, 0xe787b3#32),
   (0x80004028#64, 0x7a783#32),
   (0x8000402c#64, 0xe787b3#32)]
    terminator ⟨0x80004030#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds008_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb8#8, 0xa1#8, 0xfe#8, 0xff#8]]

theorem facts008_02 : ChainFacts (writeLog snapshotMem traceD008_02.log)
    (writeLog snapshotMem traceD008_02.log) traceD008_02.regs traceLds008_02 traceSeg008_02 := by
  have kind0 : (mkLine 0x8000401c#64 0x46783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80004020#64 0x279793#32).kind = MKind.slli := by decide
  have kind2 : (mkLine 0x80004024#64 0xe787b3#32).kind = MKind.add := by decide
  have kind3 : (mkLine 0x80004028#64 0x7a783#32).kind = MKind.lw := by decide
  have kind4 : (mkLine 0x8000402c#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg008_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run008_02 {c : Config} (h : TraceHolds traceD008_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD009 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg008_02 traceLds008_02 (by decide) facts008_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run008_02
theorem run008 {c : Config} (h : TraceHolds traceD008 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD009 c' := by
  obtain ⟨c0, s0, h0⟩ := run008_00 h
  obtain ⟨c1, s1, h1⟩ := run008_01 h0
  obtain ⟨c2, s2, h2⟩ := run008_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run008
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg009 chain
  [(0x80004170#64, 0x843603#32),
   (0x80004174#64, 0x1010513#32),
   (0x80004178#64, 0x98693#32),
   (0x8000417c#64, 0x48593#32)]

def traceLds009 : List (List (BitVec 8)) :=
  [[0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts009 : ChainFacts (writeLog snapshotMem traceD009.log)
    (writeLog snapshotMem traceD009.log) traceD009.regs traceLds009 traceSeg009 := by
  have kind0 : (mkLine 0x80004170#64 0x843603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004174#64 0x1010513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004178#64 0x98693#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000417c#64 0x48593#32).kind = MKind.addi := by decide
  simp only [traceSeg009, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run009 {c : Config} (h : TraceHolds traceD009 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD010 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg009 traceLds009 (by decide) facts009 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run009
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts010 : TraceCallFacts traceD010 0xfe5fe0ef#32
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

theorem run010 {c : Config} (h : TraceHolds traceD010 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD011 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfe5fe0ef#32 0x1fefe4#21 0xef#8 0xe0#8 0x5f#8 0xfe#8 facts010 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run010
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD011_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x80004184#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000080#64), (9, 0x87fffe10#64), (10, 0x87fffbb0#64), (11, 0x87fffe10#64), (12, 0x82000080#64), (13, 0x81000000#64), (14, 0x9#64), (15, 0xa#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 37,
    out := #[], payload := 0x0#4 }

def traceD011_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x80004184#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x82000080#64), (9, 0x87fffe10#64), (10, 0x87fffbb0#64), (11, 0x87fffe10#64), (12, 0x82000080#64), (13, 0x81000000#64), (14, 0x9#64), (15, 0xa#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 37,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg011_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds011_00 : List (List (BitVec 8)) :=
  [[0x9#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts011_00 : ChainFacts (writeLog snapshotMem traceD011.log)
    (writeLog snapshotMem traceD011.log) traceD011.regs traceLds011_00 traceSeg011_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg011_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run011_00 {c : Config} (h : TraceHolds traceD011 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD011_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg011_00 traceLds011_00 (by decide) facts011_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run011_00

#derive_case traceSeg011_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds011_01 : List (List (BitVec 8)) :=
  []

theorem facts011_01 : ChainFacts (writeLog snapshotMem traceD011_01.log)
    (writeLog snapshotMem traceD011_01.log) traceD011_01.regs traceLds011_01 traceSeg011_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg011_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run011_01 {c : Config} (h : TraceHolds traceD011_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD011_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg011_01 traceLds011_01 (by decide) facts011_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run011_01

#derive_case traceSeg011_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds011_02 : List (List (BitVec 8)) :=
  [[0x9#8, 0x0#8, 0x0#8, 0x0#8],
   [0x58#8, 0x92#8, 0xfe#8, 0xff#8]]

theorem facts011_02 : ChainFacts (writeLog snapshotMem traceD011_02.log)
    (writeLog snapshotMem traceD011_02.log) traceD011_02.regs traceLds011_02 traceSeg011_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg011_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run011_02 {c : Config} (h : TraceHolds traceD011_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD012 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg011_02 traceLds011_02 (by decide) facts011_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run011_02
theorem run011 {c : Config} (h : TraceHolds traceD011 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD012 c' := by
  obtain ⟨c0, s0, h0⟩ := run011_00 h
  obtain ⟨c1, s1, h1⟩ := run011_01 h0
  obtain ⟨c2, s2, h2⟩ := run011_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run011
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg012 chain
  [(0x800031b0#64, 0x863603#32),
   (0x800031b4#64, 0x6010513#32),
   (0x800031b8#64, 0xd13023#32)]

def traceLds012 : List (List (BitVec 8)) :=
  [[0xa0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts012 : ChainFacts (writeLog snapshotMem traceD012.log)
    (writeLog snapshotMem traceD012.log) traceD012.regs traceLds012 traceSeg012 := by
  have kind0 : (mkLine 0x800031b0#64 0x863603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800031b4#64 0x6010513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800031b8#64 0xd13023#32).kind = MKind.sd := by decide
  simp only [traceSeg012, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00863603
    | exact DecodeTable.decode_00d13023
    | exact DecodeTable.decode_06010513
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run012 {c : Config} (h : TraceHolds traceD012 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD013 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg012 traceLds012 (by decide) facts012 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run012
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts013 : TraceCallFacts traceD013 0xfa9ff0ef#32
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

theorem run013 {c : Config} (h : TraceHolds traceD013 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD014 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfa9ff0ef#32 0x1fffa8#21 0xef#8 0xf0#8 0x9f#8 0xfa#8 facts013 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run013
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD014_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x820000a0#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x87fffe10#64), (12, 0x820000a0#64), (13, 0x81000000#64), (14, 0x4#64), (15, 0xa#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 42,
    out := #[], payload := 0x0#4 }

def traceD014_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x820000a0#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x87fffe10#64), (12, 0x820000a0#64), (13, 0x81000000#64), (14, 0x4#64), (15, 0xa#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 42,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg014_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds014_00 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts014_00 : ChainFacts (writeLog snapshotMem traceD014.log)
    (writeLog snapshotMem traceD014.log) traceD014.regs traceLds014_00 traceSeg014_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg014_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run014_00 {c : Config} (h : TraceHolds traceD014 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD014_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg014_00 traceLds014_00 (by decide) facts014_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run014_00

#derive_case traceSeg014_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds014_01 : List (List (BitVec 8)) :=
  []

theorem facts014_01 : ChainFacts (writeLog snapshotMem traceD014_01.log)
    (writeLog snapshotMem traceD014_01.log) traceD014_01.regs traceLds014_01 traceSeg014_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg014_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run014_01 {c : Config} (h : TraceHolds traceD014_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD014_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg014_01 traceLds014_01 (by decide) facts014_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run014_01

#derive_case traceSeg014_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds014_02 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8, 0x0#8, 0x0#8],
   [0xdc#8, 0x94#8, 0xfe#8, 0xff#8]]

theorem facts014_02 : ChainFacts (writeLog snapshotMem traceD014_02.log)
    (writeLog snapshotMem traceD014_02.log) traceD014_02.regs traceLds014_02 traceSeg014_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg014_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run014_02 {c : Config} (h : TraceHolds traceD014_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD015 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg014_02 traceLds014_02 (by decide) facts014_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run014_02
theorem run014 {c : Config} (h : TraceHolds traceD014 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD015 c' := by
  obtain ⟨c0, s0, h0⟩ := run014_00 h
  obtain ⟨c1, s1, h1⟩ := run014_01 h0
  obtain ⟨c2, s2, h2⟩ := run014_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run014
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg015 chain
  [(0x80003434#64, 0x863583#32),
   (0x80003438#64, 0x68513#32),
   (0x8000343c#64, 0xf010613#32)]

def traceLds015 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts015 : ChainFacts (writeLog snapshotMem traceD015.log)
    (writeLog snapshotMem traceD015.log) traceD015.regs traceLds015 traceSeg015 := by
  have kind0 : (mkLine 0x80003434#64 0x863583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80003438#64 0x68513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000343c#64 0xf010613#32).kind = MKind.addi := by decide
  simp only [traceSeg015, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00068513
    | exact DecodeTable.decode_00863583
    | exact DecodeTable.decode_0f010613
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run015 {c : Config} (h : TraceHolds traceD015 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD016 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg015 traceLds015 (by decide) facts015 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run015
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts016 : TraceCallFacts traceD016 0xfd0ff0ef#32
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

theorem run016 {c : Config} (h : TraceHolds traceD016 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD017 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfd0ff0ef#32 0x1ff7d0#21 0xef#8 0xf0#8 0xf#8 0xfd#8 facts016 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run016
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD017_01 : TraceData :=
  { pc := 0x80002c14#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 42,
    out := #[], payload := 0x0#4 }

def traceD017_02 : TraceData :=
  { pc := 0x80002c34#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD017_03 : TraceData :=
  { pc := 0x80002c48#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD017_04 : TraceData :=
  { pc := 0x80002c60#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0x0#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg017_00 chain
  []
    terminator ⟨0x80002c10#64, 0x0c050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0c#8, .br bop.BEQ false, 10, 0, 0x00c4#13, 0#21, 0#12⟩

def traceLds017_00 : List (List (BitVec 8)) :=
  []

theorem facts017_00 : ChainFacts (writeLog snapshotMem traceD017.log)
    (writeLog snapshotMem traceD017.log) traceD017.regs traceLds017_00 traceSeg017_00 := by
  simp only [traceSeg017_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0c050263
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run017_00 {c : Config} (h : TraceHolds traceD017 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD017_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg017_00 traceLds017_00 (by decide) facts017_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run017_00

#derive_case traceSeg017_01 chain
  [(0x80002c14#64, 0xfc010113#32),
   (0x80002c18#64, 0x1313c23#32),
   (0x80002c1c#64, 0x1413823#32),
   (0x80002c20#64, 0x1513423#32),
   (0x80002c24#64, 0x2113c23#32),
   (0x80002c28#64, 0x2813823#32),
   (0x80002c2c#64, 0x2913423#32),
   (0x80002c30#64, 0x3213023#32)]

def traceLds017_01 : List (List (BitVec 8)) :=
  []

theorem facts017_01 : ChainFacts (writeLog snapshotMem traceD017_01.log)
    (writeLog snapshotMem traceD017_01.log) traceD017_01.regs traceLds017_01 traceSeg017_01 := by
  have kind0 : (mkLine 0x80002c14#64 0xfc010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c18#64 0x1313c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002c1c#64 0x1413823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80002c20#64 0x1513423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80002c24#64 0x2113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80002c28#64 0x2813823#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80002c2c#64 0x2913423#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80002c30#64 0x3213023#32).kind = MKind.sd := by decide
  simp only [traceSeg017_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run017_01 {c : Config} (h : TraceHolds traceD017_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD017_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg017_01 traceLds017_01 (by decide) facts017_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run017_01

#derive_case traceSeg017_02 chain
  [(0x80002c34#64, 0x50a13#32),
   (0x80002c38#64, 0x58993#32),
   (0x80002c3c#64, 0x60a93#32),
   (0x80002c40#64, 0xa2903#32)]
    terminator ⟨0x80002c44#64, 0x09205063#32, 0x63#8, 0x50#8, 0x20#8, 0x09#8, .br bop.BGE false, 0, 18, 0x0080#13, 0#21, 0#12⟩

def traceLds017_02 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts017_02 : ChainFacts (writeLog snapshotMem traceD017_02.log)
    (writeLog snapshotMem traceD017_02.log) traceD017_02.regs traceLds017_02 traceSeg017_02 := by
  have kind0 : (mkLine 0x80002c34#64 0x50a13#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c38#64 0x58993#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002c3c#64 0x60a93#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80002c40#64 0xa2903#32).kind = MKind.lw := by decide
  simp only [traceSeg017_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run017_02 {c : Config} (h : TraceHolds traceD017_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD017_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg017_02 traceLds017_02 (by decide) facts017_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run017_02

#derive_case traceSeg017_03 chain
  [(0x80002c48#64, 0x8a3483#32),
   (0x80002c4c#64, 0x413#32)]
    terminator ⟨0x80002c50#64, 0x0100006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x01#8, .j, 0, 0, 0#13, 0x000010#21, 0#12⟩

def traceLds017_03 : List (List (BitVec 8)) :=
  [[0x40#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts017_03 : ChainFacts (writeLog snapshotMem traceD017_03.log)
    (writeLog snapshotMem traceD017_03.log) traceD017_03.regs traceLds017_03 traceSeg017_03 := by
  have kind0 : (mkLine 0x80002c48#64 0x8a3483#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c4c#64 0x413#32).kind = MKind.addi := by decide
  simp only [traceSeg017_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000413
    | exact DecodeTable.decode_008a3483
    | exact DecodeTable.decode_0100006f
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run017_03 {c : Config} (h : TraceHolds traceD017_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD017_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg017_03 traceLds017_03 (by decide) facts017_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run017_03

#derive_case traceSeg017_04 chain
  [(0x80002c60#64, 0x4b503#32),
   (0x80002c64#64, 0x98593#32)]

def traceLds017_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts017_04 : ChainFacts (writeLog snapshotMem traceD017_04.log)
    (writeLog snapshotMem traceD017_04.log) traceD017_04.regs traceLds017_04 traceSeg017_04 := by
  have kind0 : (mkLine 0x80002c60#64 0x4b503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c64#64 0x98593#32).kind = MKind.addi := by decide
  simp only [traceSeg017_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0004b503
    | exact DecodeTable.decode_00098593
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run017_04 {c : Config} (h : TraceHolds traceD017_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD018 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg017_04 traceLds017_04 (by decide) facts017_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run017_04
theorem run017 {c : Config} (h : TraceHolds traceD017 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD018 c' := by
  obtain ⟨c0, s0, h0⟩ := run017_00 h
  obtain ⟨c1, s1, h1⟩ := run017_01 h0
  obtain ⟨c2, s2, h2⟩ := run017_02 h1
  obtain ⟨c3, s3, h3⟩ := run017_03 h2
  obtain ⟨c4, s4, h4⟩ := run017_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run017
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts018 : TraceCallFacts traceD018 0x238040ef#32
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

theorem run018 {c : Config} (h : TraceHolds traceD018 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x238040ef#32 0x4238#21 0xef#8 0x40#8 0x80#8 0x23#8 facts018 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run018
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD019_01 : TraceData :=
  { pc := 0x80006eb0#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x0#64), (6, 0x0#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x0#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_02 : TraceData :=
  { pc := 0x80006fac#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_03 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_04 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000201#64), (11, 0x81000211#64), (12, 0x70#64), (13, 0x70#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_05 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000201#64), (11, 0x81000211#64), (12, 0x70#64), (13, 0x70#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_06 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000202#64), (11, 0x81000212#64), (12, 0x72#64), (13, 0x72#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_07 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000202#64), (11, 0x81000212#64), (12, 0x72#64), (13, 0x72#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_08 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000203#64), (11, 0x81000213#64), (12, 0x69#64), (13, 0x69#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_09 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000203#64), (11, 0x81000213#64), (12, 0x69#64), (13, 0x69#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_10 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000204#64), (11, 0x81000214#64), (12, 0x6e#64), (13, 0x6e#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_11 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000204#64), (11, 0x81000214#64), (12, 0x6e#64), (13, 0x6e#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_12 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000205#64), (11, 0x81000215#64), (12, 0x74#64), (13, 0x74#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_13 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000205#64), (11, 0x81000215#64), (12, 0x74#64), (13, 0x74#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD019_14 : TraceData :=
  { pc := 0x80006f9c#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000206#64), (11, 0x81000216#64), (12, 0x0#64), (13, 0x6c#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg019_00 chain
  [(0x80006ea0#64, 0xb56733#32),
   (0x80006ea4#64, 0xfff00393#32),
   (0x80006ea8#64, 0x777713#32)]
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE false, 14, 0, 0x00d8#13, 0#21, 0#12⟩

def traceLds019_00 : List (List (BitVec 8)) :=
  []

theorem facts019_00 : ChainFacts (writeLog snapshotMem traceD019.log)
    (writeLog snapshotMem traceD019.log) traceD019.regs traceLds019_00 traceSeg019_00 := by
  have kind0 : (mkLine 0x80006ea0#64 0xb56733#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x80006ea4#64 0xfff00393#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006ea8#64 0x777713#32).kind = MKind.andi := by decide
  simp only [traceSeg019_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_00 {c : Config} (h : TraceHolds traceD019 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_00 traceLds019_00 (by decide) facts019_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_00

#derive_case traceSeg019_01 chain
  [(0x80006eb0#64, 0x14797#32),
   (0x80006eb4#64, 0xdd07b783#32),
   (0x80006eb8#64, 0x53603#32),
   (0x80006ebc#64, 0x5b683#32),
   (0x80006ec0#64, 0xf672b3#32),
   (0x80006ec4#64, 0xf66333#32),
   (0x80006ec8#64, 0xf282b3#32),
   (0x80006ecc#64, 0x62e2b3#32)]
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE true, 5, 7, 0x00dc#13, 0#21, 0#12⟩

def traceLds019_01 : List (List (BitVec 8)) :=
  [[0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x0#8, 0x0#8, 0x0#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8]]

theorem facts019_01 : ChainFacts (writeLog snapshotMem traceD019_01.log)
    (writeLog snapshotMem traceD019_01.log) traceD019_01.regs traceLds019_01 traceSeg019_01 := by
  have kind0 : (mkLine 0x80006eb0#64 0x14797#32).kind = MKind.auipc := by decide
  have kind1 : (mkLine 0x80006eb4#64 0xdd07b783#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80006eb8#64 0x53603#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80006ebc#64 0x5b683#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80006ec0#64 0xf672b3#32).kind = MKind.and := by decide
  have kind5 : (mkLine 0x80006ec4#64 0xf66333#32).kind = MKind.or := by decide
  have kind6 : (mkLine 0x80006ec8#64 0xf282b3#32).kind = MKind.add := by decide
  have kind7 : (mkLine 0x80006ecc#64 0x62e2b3#32).kind = MKind.or := by decide
  simp only [traceSeg019_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_01 {c : Config} (h : TraceHolds traceD019_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_01 traceLds019_01 (by decide) facts019_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_01

#derive_case traceSeg019_02 chain
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE true, 12, 13, 0x1fd8#13, 0#21, 0#12⟩

def traceLds019_02 : List (List (BitVec 8)) :=
  []

theorem facts019_02 : ChainFacts (writeLog snapshotMem traceD019_02.log)
    (writeLog snapshotMem traceD019_02.log) traceD019_02.regs traceLds019_02 traceSeg019_02 := by
  simp only [traceSeg019_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fcd61ce3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_02 {c : Config} (h : TraceHolds traceD019_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_02 traceLds019_02 (by decide) facts019_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_02

#derive_case traceSeg019_03 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_03 : List (List (BitVec 8)) :=
  [[0x70#8],
   [0x70#8]]

theorem facts019_03 : ChainFacts (writeLog snapshotMem traceD019_03.log)
    (writeLog snapshotMem traceD019_03.log) traceD019_03.regs traceLds019_03 traceSeg019_03 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_03, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_03 {c : Config} (h : TraceHolds traceD019_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_03 traceLds019_03 (by decide) facts019_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_03

#derive_case traceSeg019_04 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds019_04 : List (List (BitVec 8)) :=
  []

theorem facts019_04 : ChainFacts (writeLog snapshotMem traceD019_04.log)
    (writeLog snapshotMem traceD019_04.log) traceD019_04.regs traceLds019_04 traceSeg019_04 := by
  simp only [traceSeg019_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_04 {c : Config} (h : TraceHolds traceD019_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_04 traceLds019_04 (by decide) facts019_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_04

#derive_case traceSeg019_05 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_05 : List (List (BitVec 8)) :=
  [[0x72#8],
   [0x72#8]]

theorem facts019_05 : ChainFacts (writeLog snapshotMem traceD019_05.log)
    (writeLog snapshotMem traceD019_05.log) traceD019_05.regs traceLds019_05 traceSeg019_05 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_05, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_05 {c : Config} (h : TraceHolds traceD019_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_05 traceLds019_05 (by decide) facts019_05 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_05

#derive_case traceSeg019_06 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds019_06 : List (List (BitVec 8)) :=
  []

theorem facts019_06 : ChainFacts (writeLog snapshotMem traceD019_06.log)
    (writeLog snapshotMem traceD019_06.log) traceD019_06.regs traceLds019_06 traceSeg019_06 := by
  simp only [traceSeg019_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_06 {c : Config} (h : TraceHolds traceD019_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_06 traceLds019_06 (by decide) facts019_06 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_06

#derive_case traceSeg019_07 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_07 : List (List (BitVec 8)) :=
  [[0x69#8],
   [0x69#8]]

theorem facts019_07 : ChainFacts (writeLog snapshotMem traceD019_07.log)
    (writeLog snapshotMem traceD019_07.log) traceD019_07.regs traceLds019_07 traceSeg019_07 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_07, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_07 {c : Config} (h : TraceHolds traceD019_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_08 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_07 traceLds019_07 (by decide) facts019_07 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_07

#derive_case traceSeg019_08 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds019_08 : List (List (BitVec 8)) :=
  []

theorem facts019_08 : ChainFacts (writeLog snapshotMem traceD019_08.log)
    (writeLog snapshotMem traceD019_08.log) traceD019_08.regs traceLds019_08 traceSeg019_08 := by
  simp only [traceSeg019_08, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_08 {c : Config} (h : TraceHolds traceD019_08 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_09 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_08 traceLds019_08 (by decide) facts019_08 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_08

#derive_case traceSeg019_09 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_09 : List (List (BitVec 8)) :=
  [[0x6e#8],
   [0x6e#8]]

theorem facts019_09 : ChainFacts (writeLog snapshotMem traceD019_09.log)
    (writeLog snapshotMem traceD019_09.log) traceD019_09.regs traceLds019_09 traceSeg019_09 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_09, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_09 {c : Config} (h : TraceHolds traceD019_09 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_10 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_09 traceLds019_09 (by decide) facts019_09 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_09

#derive_case traceSeg019_10 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds019_10 : List (List (BitVec 8)) :=
  []

theorem facts019_10 : ChainFacts (writeLog snapshotMem traceD019_10.log)
    (writeLog snapshotMem traceD019_10.log) traceD019_10.regs traceLds019_10 traceSeg019_10 := by
  simp only [traceSeg019_10, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_10 {c : Config} (h : TraceHolds traceD019_10 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_11 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_10 traceLds019_10 (by decide) facts019_10 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_10

#derive_case traceSeg019_11 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_11 : List (List (BitVec 8)) :=
  [[0x74#8],
   [0x74#8]]

theorem facts019_11 : ChainFacts (writeLog snapshotMem traceD019_11.log)
    (writeLog snapshotMem traceD019_11.log) traceD019_11.regs traceLds019_11 traceSeg019_11 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_11, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_11 {c : Config} (h : TraceHolds traceD019_11 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_12 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_11 traceLds019_11 (by decide) facts019_11 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_11

#derive_case traceSeg019_12 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds019_12 : List (List (BitVec 8)) :=
  []

theorem facts019_12 : ChainFacts (writeLog snapshotMem traceD019_12.log)
    (writeLog snapshotMem traceD019_12.log) traceD019_12.regs traceLds019_12 traceSeg019_12 := by
  simp only [traceSeg019_12, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_12 {c : Config} (h : TraceHolds traceD019_12 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_13 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_12 traceLds019_12 (by decide) facts019_12 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_12

#derive_case traceSeg019_13 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE true, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds019_13 : List (List (BitVec 8)) :=
  [[0x0#8],
   [0x6c#8]]

theorem facts019_13 : ChainFacts (writeLog snapshotMem traceD019_13.log)
    (writeLog snapshotMem traceD019_13.log) traceD019_13.regs traceLds019_13 traceSeg019_13 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg019_13, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run019_13 {c : Config} (h : TraceHolds traceD019_13 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD019_14 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_13 traceLds019_13 (by decide) facts019_13 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_13

#derive_case traceSeg019_14 chain
  [(0x80006f9c#64, 0x40d60533#32)]
    terminator ⟨0x80006fa0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds019_14 : List (List (BitVec 8)) :=
  []

theorem facts019_14 : ChainFacts (writeLog snapshotMem traceD019_14.log)
    (writeLog snapshotMem traceD019_14.log) traceD019_14.regs traceLds019_14 traceSeg019_14 := by
  have kind0 : (mkLine 0x80006f9c#64 0x40d60533#32).kind = MKind.sub := by decide
  simp only [traceSeg019_14, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_40d60533
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run019_14 {c : Config} (h : TraceHolds traceD019_14 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD020 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg019_14 traceLds019_14 (by decide) facts019_14 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run019_14
theorem run019 {c : Config} (h : TraceHolds traceD019 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD020 c' := by
  obtain ⟨c0, s0, h0⟩ := run019_00 h
  obtain ⟨c1, s1, h1⟩ := run019_01 h0
  obtain ⟨c2, s2, h2⟩ := run019_02 h1
  obtain ⟨c3, s3, h3⟩ := run019_03 h2
  obtain ⟨c4, s4, h4⟩ := run019_04 h3
  obtain ⟨c5, s5, h5⟩ := run019_05 h4
  obtain ⟨c6, s6, h6⟩ := run019_06 h5
  obtain ⟨c7, s7, h7⟩ := run019_07 h6
  obtain ⟨c8, s8, h8⟩ := run019_08 h7
  obtain ⟨c9, s9, h9⟩ := run019_09 h8
  obtain ⟨c10, s10, h10⟩ := run019_10 h9
  obtain ⟨c11, s11, h11⟩ := run019_11 h10
  obtain ⟨c12, s12, h12⟩ := run019_12 h11
  obtain ⟨c13, s13, h13⟩ := run019_13 h12
  obtain ⟨c14, s14, h14⟩ := run019_14 h13
  exact ⟨c14, ((((((((((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).trans s10).trans s11).trans s12).trans s13).trans s14, h14⟩

#print axioms run019
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg020 chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE true, 10, 0, 0x1fe8#13, 0#21, 0#12⟩ ;;
  [(0x80002c54#64, 0x140413#32),
   (0x80002c58#64, 0x848493#32)]
    terminator ⟨0x80002c5c#64, 0x07240463#32, 0x63#8, 0x04#8, 0x24#8, 0x07#8, .br bop.BEQ false, 8, 18, 0x0068#13, 0#21, 0#12⟩ ;;
  [(0x80002c60#64, 0x4b503#32),
   (0x80002c64#64, 0x98593#32)]

def traceLds020 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts020 : ChainFacts (writeLog snapshotMem traceD020.log)
    (writeLog snapshotMem traceD020.log) traceD020.regs traceLds020 traceSeg020 := by
  have kind0 : (mkLine 0x80002c54#64 0x140413#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c58#64 0x848493#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002c60#64 0x4b503#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002c64#64 0x98593#32).kind = MKind.addi := by decide
  simp only [traceSeg020, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run020 {c : Config} (h : TraceHolds traceD020 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD021 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg020 traceLds020 (by decide) facts020 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run020
end Vsa.Sim.OutputAliasLoaded
