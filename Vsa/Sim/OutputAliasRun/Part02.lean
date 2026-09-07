import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part03
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part11
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part27
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch02Part26
import Vsa.Sim.DecodeTable.Batch02Part27
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch04Part01
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch04Part04
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part10
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part19
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part23
import Vsa.Sim.DecodeTable.Batch04Part25
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part03
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part15
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch05Part25
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part04
import Vsa.Sim.DecodeTable.Batch06Part05
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part22
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part09
import Vsa.Sim.DecodeTable.Batch07Part10
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part25
import Vsa.Sim.DecodeTable.Batch07Part26
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part29
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part11
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part14
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch10Part01
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part20
import Vsa.Sim.DecodeTable.Batch11Part25
import Vsa.Sim.DecodeTable.Batch11Part27
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch13Part13
import Vsa.Sim.DecodeTable.Batch13Part22
import Vsa.Sim.DecodeTable.Batch14Part12
import Vsa.Sim.DecodeTable.Batch14Part29
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part24
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part04
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch16Part28
import Vsa.Sim.DecodeTable.Batch16Part29
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

theorem facts041 : TraceCallFacts traceD041 0x885f80ef#32
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

theorem run041 {c : Config} (h : TraceHolds traceD041 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD042 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x885f80ef#32 0x1f8884#21 0xef#8 0x80#8 0x5f#8 0x88#8 facts041 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run041
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg042 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds042 : List (List (BitVec 8)) :=
  []

theorem facts042 : ChainFacts (writeLog snapshotMem traceD042.log)
    (writeLog snapshotMem traceD042.log) traceD042.regs traceLds042 traceSeg042 := by
  simp only [traceSeg042, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run042 {c : Config} (h : TraceHolds traceD042 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD043 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg042 traceLds042 (by decide) facts042 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run042
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg043 chain
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

def traceLds043 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts043 : ChainFacts (writeLog snapshotMem traceD043.log)
    (writeLog snapshotMem traceD043.log) traceD043.regs traceLds043 traceSeg043 := by
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
  simp only [traceSeg043, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run043 {c : Config} (h : TraceHolds traceD043 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD044 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg043 traceLds043 (by decide) facts043 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run043
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts044 : TraceCallFacts traceD044 0x18d000ef#32
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

theorem run044 {c : Config} (h : TraceHolds traceD044 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x18d000ef#32 0x98c#21 0xef#8 0x0#8 0xd0#8 0x18#8 facts044 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run044
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD045_01 : TraceData :=
  { pc := 0x8000f0e4#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0xffffffffffffffff#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 78,
    out := #[], payload := 0x0#4 }

def traceD045_02 : TraceData :=
  { pc := 0x8000f0ec#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 78,
    out := #[], payload := 0x0#4 }

def traceD045_03 : TraceData :=
  { pc := 0x8000f100#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 79,
    out := #[], payload := 0x0#4 }

def traceD045_04 : TraceData :=
  { pc := 0x8000f108#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0xa#64), (14, 0x8001bb97#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 79,
    out := #[], payload := 0x0#4 }

def traceD045_05 : TraceData :=
  { pc := 0x8000f118#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x8028000000000000#64), (14, 0x0#64), (15, 0x200a#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 79,
    out := #[], payload := 0x0#4 }

def traceD045_06 : TraceData :=
  { pc := 0x8000f120#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x8028000000000000#64), (14, 0x0#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 79,
    out := #[], payload := 0x0#4 }

def traceD045_07 : TraceData :=
  { pc := 0x8000f134#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x2000#64), (12, 0x8001bb20#64), (13, 0x1#64), (14, 0x8001bb97#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 79,
    out := #[], payload := 0x0#4 }

def traceD045_08 : TraceData :=
  { pc := 0x8000f154#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb98#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x1#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 82,
    out := #[], payload := 0x0#4 }

def traceD045_09 : TraceData :=
  { pc := 0x8000f1d0#64,
    regs := [(1, 0x8000e740#64), (2, 0x87fff6b0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb98#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x1#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 82,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg045_00 chain
  [(0x8000f0c8#64, 0xfd010113#32),
   (0x8000f0cc#64, 0x2813023#32),
   (0x8000f0d0#64, 0x913c23#32),
   (0x8000f0d4#64, 0x2113423#32),
   (0x8000f0d8#64, 0x50493#32),
   (0x8000f0dc#64, 0x58413#32)]
    terminator ⟨0x8000f0e0#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds045_00 : List (List (BitVec 8)) :=
  []

theorem facts045_00 : ChainFacts (writeLog snapshotMem traceD045.log)
    (writeLog snapshotMem traceD045.log) traceD045.regs traceLds045_00 traceSeg045_00 := by
  have kind0 : (mkLine 0x8000f0c8#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f0cc#64 0x2813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000f0d0#64 0x913c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000f0d4#64 0x2113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000f0d8#64 0x50493#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x8000f0dc#64 0x58413#32).kind = MKind.addi := by decide
  simp only [traceSeg045_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run045_00 {c : Config} (h : TraceHolds traceD045 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_00 traceLds045_00 (by decide) facts045_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_00

#derive_case traceSeg045_01 chain
  [(0x8000f0e4#64, 0x4853783#32)]
    terminator ⟨0x8000f0e8#64, 0x12078263#32, 0x63#8, 0x82#8, 0x07#8, 0x12#8, .br bop.BEQ false, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds045_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts045_01 : ChainFacts (writeLog snapshotMem traceD045_01.log)
    (writeLog snapshotMem traceD045_01.log) traceD045_01.regs traceLds045_01 traceSeg045_01 := by
  have kind0 : (mkLine 0x8000f0e4#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg045_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact DecodeTable.decode_12078263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run045_01 {c : Config} (h : TraceHolds traceD045_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_01 traceLds045_01 (by decide) facts045_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_01

#derive_case traceSeg045_02 chain
  [(0x8000f0ec#64, 0x2862703#32),
   (0x8000f0f0#64, 0x1061783#32),
   (0x8000f0f4#64, 0xe62623#32),
   (0x8000f0f8#64, 0x87f713#32)]
    terminator ⟨0x8000f0fc#64, 0x08070663#32, 0x63#8, 0x06#8, 0x07#8, 0x08#8, .br bop.BEQ false, 14, 0, 0x008c#13, 0#21, 0#12⟩

def traceLds045_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8]]

theorem facts045_02 : ChainFacts (writeLog snapshotMem traceD045_02.log)
    (writeLog snapshotMem traceD045_02.log) traceD045_02.regs traceLds045_02 traceSeg045_02 := by
  have kind0 : (mkLine 0x8000f0ec#64 0x2862703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000f0f0#64 0x1061783#32).kind = MKind.lh := by decide
  have kind2 : (mkLine 0x8000f0f4#64 0xe62623#32).kind = MKind.sw := by decide
  have kind3 : (mkLine 0x8000f0f8#64 0x87f713#32).kind = MKind.andi := by decide
  simp only [traceSeg045_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run045_02 {c : Config} (h : TraceHolds traceD045_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_02 traceLds045_02 (by decide) facts045_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_02

#derive_case traceSeg045_03 chain
  [(0x8000f100#64, 0x1863703#32)]
    terminator ⟨0x8000f104#64, 0x08070263#32, 0x63#8, 0x02#8, 0x07#8, 0x08#8, .br bop.BEQ false, 14, 0, 0x0084#13, 0#21, 0#12⟩

def traceLds045_03 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts045_03 : ChainFacts (writeLog snapshotMem traceD045_03.log)
    (writeLog snapshotMem traceD045_03.log) traceD045_03.regs traceLds045_03 traceSeg045_03 := by
  have kind0 : (mkLine 0x8000f100#64 0x1863703#32).kind = MKind.ld := by decide
  simp only [traceSeg045_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01863703
    | exact DecodeTable.decode_08070263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run045_03 {c : Config} (h : TraceHolds traceD045_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_03 traceLds045_03 (by decide) facts045_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_03

#derive_case traceSeg045_04 chain
  [(0x8000f108#64, 0x3279693#32),
   (0x8000f10c#64, 0xb062703#32),
   (0x8000f110#64, 0x25b7#32)]
    terminator ⟨0x8000f114#64, 0x0a06d063#32, 0x63#8, 0xd0#8, 0x06#8, 0x0a#8, .br bop.BGE false, 13, 0, 0x00a0#13, 0#21, 0#12⟩

def traceLds045_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts045_04 : ChainFacts (writeLog snapshotMem traceD045_04.log)
    (writeLog snapshotMem traceD045_04.log) traceD045_04.regs traceLds045_04 traceSeg045_04 := by
  have kind0 : (mkLine 0x8000f108#64 0x3279693#32).kind = MKind.slli := by decide
  have kind1 : (mkLine 0x8000f10c#64 0xb062703#32).kind = MKind.lw := by decide
  have kind2 : (mkLine 0x8000f110#64 0x25b7#32).kind = MKind.lui := by decide
  simp only [traceSeg045_04, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run045_04 {c : Config} (h : TraceHolds traceD045_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_04 traceLds045_04 (by decide) facts045_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_04

#derive_case traceSeg045_05 chain
  [(0x8000f118#64, 0x3271793#32)]
    terminator ⟨0x8000f11c#64, 0x0c07c263#32, 0x63#8, 0xc2#8, 0x07#8, 0x0c#8, .br bop.BLT false, 15, 0, 0x00c4#13, 0#21, 0#12⟩

def traceLds045_05 : List (List (BitVec 8)) :=
  []

theorem facts045_05 : ChainFacts (writeLog snapshotMem traceD045_05.log)
    (writeLog snapshotMem traceD045_05.log) traceD045_05.regs traceLds045_05 traceSeg045_05 := by
  have kind0 : (mkLine 0x8000f118#64 0x3271793#32).kind = MKind.slli := by decide
  simp only [traceSeg045_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_03271793
    | exact DecodeTable.decode_0c07c263
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run045_05 {c : Config} (h : TraceHolds traceD045_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_05 traceLds045_05 (by decide) facts045_05 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_05

#derive_case traceSeg045_06 chain
  [(0x8000f120#64, 0x63703#32),
   (0x8000f124#64, 0x1863783#32),
   (0x8000f128#64, 0x2062683#32),
   (0x8000f12c#64, 0x40f707bb#32)]
    terminator ⟨0x8000f130#64, 0x0ad7dc63#32, 0x63#8, 0xdc#8, 0xd7#8, 0x0a#8, .br bop.BGE false, 15, 13, 0x00b8#13, 0#21, 0#12⟩

def traceLds045_06 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts045_06 : ChainFacts (writeLog snapshotMem traceD045_06.log)
    (writeLog snapshotMem traceD045_06.log) traceD045_06.regs traceLds045_06 traceSeg045_06 := by
  have kind0 : (mkLine 0x8000f120#64 0x63703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000f124#64 0x1863783#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000f128#64 0x2062683#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x8000f12c#64 0x40f707bb#32).kind = MKind.subw := by decide
  simp only [traceSeg045_06, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run045_06 {c : Config} (h : TraceHolds traceD045_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_06 traceLds045_06 (by decide) facts045_06 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_06

#derive_case traceSeg045_07 chain
  [(0x8000f134#64, 0x17879b#32),
   (0x8000f138#64, 0xc62683#32),
   (0x8000f13c#64, 0x170593#32),
   (0x8000f140#64, 0xb63023#32),
   (0x8000f144#64, 0xfff6869b#32),
   (0x8000f148#64, 0xd62623#32),
   (0x8000f14c#64, 0x870023#32),
   (0x8000f150#64, 0x2062703#32)]

def traceLds045_07 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts045_07 : ChainFacts (writeLog snapshotMem traceD045_07.log)
    (writeLog snapshotMem traceD045_07.log) traceD045_07.regs traceLds045_07 traceSeg045_07 := by
  have kind0 : (mkLine 0x8000f134#64 0x17879b#32).kind = MKind.addiw := by decide
  have kind1 : (mkLine 0x8000f138#64 0xc62683#32).kind = MKind.lw := by decide
  have kind2 : (mkLine 0x8000f13c#64 0x170593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000f140#64 0xb63023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000f144#64 0xfff6869b#32).kind = MKind.addiw := by decide
  have kind5 : (mkLine 0x8000f148#64 0xd62623#32).kind = MKind.sw := by decide
  have kind6 : (mkLine 0x8000f14c#64 0x870023#32).kind = MKind.sb := by decide
  have kind7 : (mkLine 0x8000f150#64 0x2062703#32).kind = MKind.lw := by decide
  simp only [traceSeg045_07, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run045_07 {c : Config} (h : TraceHolds traceD045_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_08 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_07 traceLds045_07 (by decide) facts045_07 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_07

#derive_case traceSeg045_08 chain
  [(0x8000f154#64, 0xff47413#32)]
    terminator ⟨0x8000f158#64, 0x06f70c63#32, 0x63#8, 0x0c#8, 0xf7#8, 0x06#8, .br bop.BEQ true, 14, 15, 0x0078#13, 0#21, 0#12⟩

def traceLds045_08 : List (List (BitVec 8)) :=
  []

theorem facts045_08 : ChainFacts (writeLog snapshotMem traceD045_08.log)
    (writeLog snapshotMem traceD045_08.log) traceD045_08.regs traceLds045_08 traceSeg045_08 := by
  have kind0 : (mkLine 0x8000f154#64 0xff47413#32).kind = MKind.andi := by decide
  simp only [traceSeg045_08, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_06f70c63
    | exact DecodeTable.decode_0ff47413
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run045_08 {c : Config} (h : TraceHolds traceD045_08 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD045_09 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_08 traceLds045_08 (by decide) facts045_08 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_08

#derive_case traceSeg045_09 chain
  [(0x8000f1d0#64, 0x60593#32),
   (0x8000f1d4#64, 0x48513#32)]

def traceLds045_09 : List (List (BitVec 8)) :=
  []

theorem facts045_09 : ChainFacts (writeLog snapshotMem traceD045_09.log)
    (writeLog snapshotMem traceD045_09.log) traceD045_09.regs traceLds045_09 traceSeg045_09 := by
  have kind0 : (mkLine 0x8000f1d0#64 0x60593#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f1d4#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg045_09, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00060593
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run045_09 {c : Config} (h : TraceHolds traceD045_09 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD046 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg045_09 traceLds045_09 (by decide) facts045_09 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run045_09
theorem run045 {c : Config} (h : TraceHolds traceD045 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD046 c' := by
  obtain ⟨c0, s0, h0⟩ := run045_00 h
  obtain ⟨c1, s1, h1⟩ := run045_01 h0
  obtain ⟨c2, s2, h2⟩ := run045_02 h1
  obtain ⟨c3, s3, h3⟩ := run045_03 h2
  obtain ⟨c4, s4, h4⟩ := run045_04 h3
  obtain ⟨c5, s5, h5⟩ := run045_05 h4
  obtain ⟨c6, s6, h6⟩ := run045_06 h5
  obtain ⟨c7, s7, h7⟩ := run045_07 h6
  obtain ⟨c8, s8, h8⟩ := run045_08 h7
  obtain ⟨c9, s9, h9⟩ := run045_09 h8
  exact ⟨c9, (((((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9, h9⟩

#print axioms run045
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts046 : TraceCallFacts traceD046 0xbf5ff0ef#32
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

theorem run046 {c : Config} (h : TraceHolds traceD046 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xbf5ff0ef#32 0x1ffbf4#21 0xef#8 0xf0#8 0x5f#8 0xbf#8 facts046 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run046
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD047_01 : TraceData :=
  { pc := 0x8000eddc#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x8001b538#64), (15, 0x1#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 83,
    out := #[], payload := 0x0#4 }

def traceD047_02 : TraceData :=
  { pc := 0x8000ede4#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0xffffffffffffffff#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 83,
    out := #[], payload := 0x0#4 }

def traceD047_03 : TraceData :=
  { pc := 0x8000edf0#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x200a#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 83,
    out := #[], payload := 0x0#4 }

def traceD047_04 : TraceData :=
  { pc := 0x8000edfc#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x200a#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 83,
    out := #[], payload := 0x0#4 }

def traceD047_05 : TraceData :=
  { pc := 0x8000ee40#64,
    regs := [(1, 0x8000f1dc#64), (2, 0x87fff690#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0xa#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 83,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg047_00 chain
  [(0x8000edcc#64, 0xfe010113#32),
   (0x8000edd0#64, 0x113c23#32),
   (0x8000edd4#64, 0x50713#32)]
    terminator ⟨0x8000edd8#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds047_00 : List (List (BitVec 8)) :=
  []

theorem facts047_00 : ChainFacts (writeLog snapshotMem traceD047.log)
    (writeLog snapshotMem traceD047.log) traceD047.regs traceLds047_00 traceSeg047_00 := by
  have kind0 : (mkLine 0x8000edcc#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000edd0#64 0x113c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000edd4#64 0x50713#32).kind = MKind.addi := by decide
  simp only [traceSeg047_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run047_00 {c : Config} (h : TraceHolds traceD047 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_00 traceLds047_00 (by decide) facts047_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_00

#derive_case traceSeg047_01 chain
  [(0x8000eddc#64, 0x4853783#32)]
    terminator ⟨0x8000ede0#64, 0x08078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x08#8, .br bop.BEQ false, 15, 0, 0x009c#13, 0#21, 0#12⟩

def traceLds047_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts047_01 : ChainFacts (writeLog snapshotMem traceD047_01.log)
    (writeLog snapshotMem traceD047_01.log) traceD047_01.regs traceLds047_01 traceSeg047_01 := by
  have kind0 : (mkLine 0x8000eddc#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg047_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact DecodeTable.decode_08078e63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run047_01 {c : Config} (h : TraceHolds traceD047_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_01 traceLds047_01 (by decide) facts047_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_01

#derive_case traceSeg047_02 chain
  [(0x8000ede4#64, 0x1059683#32),
   (0x8000ede8#64, 0x793#32)]
    terminator ⟨0x8000edec#64, 0x04068263#32, 0x63#8, 0x82#8, 0x06#8, 0x04#8, .br bop.BEQ false, 13, 0, 0x0044#13, 0#21, 0#12⟩

def traceLds047_02 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts047_02 : ChainFacts (writeLog snapshotMem traceD047_02.log)
    (writeLog snapshotMem traceD047_02.log) traceD047_02.regs traceLds047_02 traceSeg047_02 := by
  have kind0 : (mkLine 0x8000ede4#64 0x1059683#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000ede8#64 0x793#32).kind = MKind.addi := by decide
  simp only [traceSeg047_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000793
    | exact DecodeTable.decode_01059683
    | exact DecodeTable.decode_04068263
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run047_02 {c : Config} (h : TraceHolds traceD047_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_02 traceLds047_02 (by decide) facts047_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_02

#derive_case traceSeg047_03 chain
  [(0x8000edf0#64, 0xb05a783#32),
   (0x8000edf4#64, 0x17f793#32)]
    terminator ⟨0x8000edf8#64, 0x00079663#32, 0x63#8, 0x96#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds047_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts047_03 : ChainFacts (writeLog snapshotMem traceD047_03.log)
    (writeLog snapshotMem traceD047_03.log) traceD047_03.regs traceLds047_03 traceSeg047_03 := by
  have kind0 : (mkLine 0x8000edf0#64 0xb05a783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000edf4#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg047_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00079663
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_0b05a783
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run047_03 {c : Config} (h : TraceHolds traceD047_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_03 traceLds047_03 (by decide) facts047_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_03

#derive_case traceSeg047_04 chain
  [(0x8000edfc#64, 0x2006f693#32)]
    terminator ⟨0x8000ee00#64, 0x04068063#32, 0x63#8, 0x80#8, 0x06#8, 0x04#8, .br bop.BEQ true, 13, 0, 0x0040#13, 0#21, 0#12⟩

def traceLds047_04 : List (List (BitVec 8)) :=
  []

theorem facts047_04 : ChainFacts (writeLog snapshotMem traceD047_04.log)
    (writeLog snapshotMem traceD047_04.log) traceD047_04.regs traceLds047_04 traceSeg047_04 := by
  have kind0 : (mkLine 0x8000edfc#64 0x2006f693#32).kind = MKind.andi := by decide
  simp only [traceSeg047_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04068063
    | exact DecodeTable.decode_2006f693
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run047_04 {c : Config} (h : TraceHolds traceD047_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD047_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_04 traceLds047_04 (by decide) facts047_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_04

#derive_case traceSeg047_05 chain
  [(0x8000ee40#64, 0xa05b503#32),
   (0x8000ee44#64, 0xe13423#32),
   (0x8000ee48#64, 0xb13023#32)]

def traceLds047_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts047_05 : ChainFacts (writeLog snapshotMem traceD047_05.log)
    (writeLog snapshotMem traceD047_05.log) traceD047_05.regs traceLds047_05 traceSeg047_05 := by
  have kind0 : (mkLine 0x8000ee40#64 0xa05b503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee44#64 0xe13423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ee48#64 0xb13023#32).kind = MKind.sd := by decide
  simp only [traceSeg047_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00b13023
    | exact DecodeTable.decode_00e13423
    | exact DecodeTable.decode_0a05b503
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run047_05 {c : Config} (h : TraceHolds traceD047_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD048 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg047_05 traceLds047_05 (by decide) facts047_05 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run047_05
theorem run047 {c : Config} (h : TraceHolds traceD047 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD048 c' := by
  obtain ⟨c0, s0, h0⟩ := run047_00 h
  obtain ⟨c1, s1, h1⟩ := run047_01 h0
  obtain ⟨c2, s2, h2⟩ := run047_02 h1
  obtain ⟨c3, s3, h3⟩ := run047_03 h2
  obtain ⟨c4, s4, h4⟩ := run047_04 h3
  obtain ⟨c5, s5, h5⟩ := run047_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run047
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts048 : TraceCallFacts traceD048 0x994f80ef#32
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

theorem run048 {c : Config} (h : TraceHolds traceD048 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD049 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x994f80ef#32 0x1f8194#21 0xef#8 0x80#8 0x4f#8 0x99#8 facts048 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run048
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg049 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds049 : List (List (BitVec 8)) :=
  []

theorem facts049 : ChainFacts (writeLog snapshotMem traceD049.log)
    (writeLog snapshotMem traceD049.log) traceD049.regs traceLds049 traceSeg049 := by
  simp only [traceSeg049, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run049 {c : Config} (h : TraceHolds traceD049 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD050 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg049 traceLds049 (by decide) facts049 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run049
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg050 chain
  [(0x8000ee50#64, 0x813703#32),
   (0x8000ee54#64, 0x13583#32)]
    terminator ⟨0x8000ee58#64, 0xfadff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xfa#8, .j, 0, 0, 0#13, 0x1fffac#21, 0#12⟩ ;;
  [(0x8000ee04#64, 0x70513#32),
   (0x8000ee08#64, 0xb13023#32)]

def traceLds050 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts050 : ChainFacts (writeLog snapshotMem traceD050.log)
    (writeLog snapshotMem traceD050.log) traceD050.regs traceLds050 traceSeg050 := by
  have kind0 : (mkLine 0x8000ee50#64 0x813703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ee54#64 0x13583#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ee04#64 0x70513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ee08#64 0xb13023#32).kind = MKind.sd := by decide
  simp only [traceSeg050, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run050 {c : Config} (h : TraceHolds traceD050 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD051 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg050 traceLds050 (by decide) facts050 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run050
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts051 : TraceCallFacts traceD051 0xd65ff0ef#32
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

theorem run051 {c : Config} (h : TraceHolds traceD051 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD052 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xd65ff0ef#32 0x1ffd64#21 0xef#8 0xf0#8 0x5f#8 0xd6#8 facts051 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run051
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD052_01 : TraceData :=
  { pc := 0x8000ecb4#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 89,
    out := #[], payload := 0x0#4 }

def traceD052_02 : TraceData :=
  { pc := 0x8000ecc0#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x200a#64), (15, 0x8#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 90,
    out := #[], payload := 0x0#4 }

def traceD052_03 : TraceData :=
  { pc := 0x8000ece0#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 92,
    out := #[], payload := 0x0#4 }

def traceD052_04 : TraceData :=
  { pc := 0x8000ecf4#64,
    regs := [(1, 0x8000ee10#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb20#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 93,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg052_00 chain
  [(0x8000eb70#64, 0x1059703#32),
   (0x8000eb74#64, 0xfd010113#32),
   (0x8000eb78#64, 0x2813023#32),
   (0x8000eb7c#64, 0x1313423#32),
   (0x8000eb80#64, 0x2113423#32),
   (0x8000eb84#64, 0x877793#32),
   (0x8000eb88#64, 0x58413#32),
   (0x8000eb8c#64, 0x50993#32)]
    terminator ⟨0x8000eb90#64, 0x12079263#32, 0x63#8, 0x92#8, 0x07#8, 0x12#8, .br bop.BNE true, 15, 0, 0x0124#13, 0#21, 0#12⟩

def traceLds052_00 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts052_00 : ChainFacts (writeLog snapshotMem traceD052.log)
    (writeLog snapshotMem traceD052.log) traceD052.regs traceLds052_00 traceSeg052_00 := by
  have kind0 : (mkLine 0x8000eb70#64 0x1059703#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000eb74#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000eb78#64 0x2813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x8000eb7c#64 0x1313423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000eb80#64 0x2113423#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x8000eb84#64 0x877793#32).kind = MKind.andi := by decide
  have kind6 : (mkLine 0x8000eb88#64 0x58413#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000eb8c#64 0x50993#32).kind = MKind.addi := by decide
  simp only [traceSeg052_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run052_00 {c : Config} (h : TraceHolds traceD052 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD052_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg052_00 traceLds052_00 (by decide) facts052_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run052_00

#derive_case traceSeg052_01 chain
  [(0x8000ecb4#64, 0x1213823#32),
   (0x8000ecb8#64, 0x185b903#32)]
    terminator ⟨0x8000ecbc#64, 0x08090a63#32, 0x63#8, 0x0a#8, 0x09#8, 0x08#8, .br bop.BEQ false, 18, 0, 0x0094#13, 0#21, 0#12⟩

def traceLds052_01 : List (List (BitVec 8)) :=
  [[0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts052_01 : ChainFacts (writeLog snapshotMem traceD052_01.log)
    (writeLog snapshotMem traceD052_01.log) traceD052_01.regs traceLds052_01 traceSeg052_01 := by
  have kind0 : (mkLine 0x8000ecb4#64 0x1213823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecb8#64 0x185b903#32).kind = MKind.ld := by decide
  simp only [traceSeg052_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01213823
    | exact DecodeTable.decode_0185b903
    | exact DecodeTable.decode_08090a63
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run052_01 {c : Config} (h : TraceHolds traceD052_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD052_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg052_01 traceLds052_01 (by decide) facts052_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run052_01

#derive_case traceSeg052_02 chain
  [(0x8000ecc0#64, 0x913c23#32),
   (0x8000ecc4#64, 0x5b483#32),
   (0x8000ecc8#64, 0x377713#32),
   (0x8000eccc#64, 0x125b023#32),
   (0x8000ecd0#64, 0x412484bb#32),
   (0x8000ecd4#64, 0x793#32)]
    terminator ⟨0x8000ecd8#64, 0x00071463#32, 0x63#8, 0x14#8, 0x07#8, 0x00#8, .br bop.BNE true, 14, 0, 0x0008#13, 0#21, 0#12⟩

def traceLds052_02 : List (List (BitVec 8)) :=
  [[0x98#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts052_02 : ChainFacts (writeLog snapshotMem traceD052_02.log)
    (writeLog snapshotMem traceD052_02.log) traceD052_02.regs traceLds052_02 traceSeg052_02 := by
  have kind0 : (mkLine 0x8000ecc0#64 0x913c23#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ecc4#64 0x5b483#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ecc8#64 0x377713#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eccc#64 0x125b023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000ecd0#64 0x412484bb#32).kind = MKind.subw := by decide
  have kind5 : (mkLine 0x8000ecd4#64 0x793#32).kind = MKind.addi := by decide
  simp only [traceSeg052_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run052_02 {c : Config} (h : TraceHolds traceD052_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD052_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg052_02 traceLds052_02 (by decide) facts052_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run052_02

#derive_case traceSeg052_03 chain
  [(0x8000ece0#64, 0xf42623#32)]
    terminator ⟨0x8000ece4#64, 0x00904863#32, 0x63#8, 0x48#8, 0x90#8, 0x00#8, .br bop.BLT true, 0, 9, 0x0010#13, 0#21, 0#12⟩

def traceLds052_03 : List (List (BitVec 8)) :=
  []

theorem facts052_03 : ChainFacts (writeLog snapshotMem traceD052_03.log)
    (writeLog snapshotMem traceD052_03.log) traceD052_03.regs traceLds052_03 traceSeg052_03 := by
  have kind0 : (mkLine 0x8000ece0#64 0xf42623#32).kind = MKind.sw := by decide
  simp only [traceSeg052_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00904863
    | exact DecodeTable.decode_00f42623
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run052_03 {c : Config} (h : TraceHolds traceD052_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD052_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg052_03 traceLds052_03 (by decide) facts052_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run052_03

#derive_case traceSeg052_04 chain
  [(0x8000ecf4#64, 0x4043783#32),
   (0x8000ecf8#64, 0x3043583#32),
   (0x8000ecfc#64, 0x48693#32),
   (0x8000ed00#64, 0x90613#32),
   (0x8000ed04#64, 0x98513#32)]

def traceLds052_04 : List (List (BitVec 8)) :=
  [[0xd4#8, 0xef#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts052_04 : ChainFacts (writeLog snapshotMem traceD052_04.log)
    (writeLog snapshotMem traceD052_04.log) traceD052_04.regs traceLds052_04 traceSeg052_04 := by
  have kind0 : (mkLine 0x8000ecf4#64 0x4043783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000ecf8#64 0x3043583#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000ecfc#64 0x48693#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ed00#64 0x90613#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000ed04#64 0x98513#32).kind = MKind.addi := by decide
  simp only [traceSeg052_04, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run052_04 {c : Config} (h : TraceHolds traceD052_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD053 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg052_04 traceLds052_04 (by decide) facts052_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run052_04
theorem run052 {c : Config} (h : TraceHolds traceD052 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD053 c' := by
  obtain ⟨c0, s0, h0⟩ := run052_00 h
  obtain ⟨c1, s1, h1⟩ := run052_01 h0
  obtain ⟨c2, s2, h2⟩ := run052_02 h1
  obtain ⟨c3, s3, h3⟩ := run052_03 h2
  obtain ⟨c4, s4, h4⟩ := run052_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run052
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts053 : TraceCallFacts traceD053 0x780e7#32
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

theorem run053 {c : Config} (h : TraceHolds traceD053 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD054 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x780e7#32 0x0#12 15 0x8000efd4#64
    0xe7#8 0x80#8 0x7#8 0x0#8 facts053
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run053
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD054_01 : TraceData :=
  { pc := 0x8000eff8#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff630#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x8001bb20#64), (12, 0x8001bb97#64), (13, 0x0#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 94,
    out := #[], payload := 0x0#4 }

def traceD054_02 : TraceData :=
  { pc := 0x8000f018#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff630#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x1#64), (12, 0x8001bb97#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 95,
    out := #[], payload := 0x0#4 }

def traceD054_03 : TraceData :=
  { pc := 0x800104fc#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff660#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x1#64), (10, 0x8001b538#64), (11, 0x1#64), (12, 0x8001bb97#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x200a#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 95,
    out := #[], payload := 0x0#4 }

def traceD054_04 : TraceData :=
  { pc := 0x8001051c#64,
    regs := [(1, 0x8000ed0c#64), (2, 0x87fff650#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001b538#64), (9, 0x1#64), (10, 0x1#64), (11, 0x8001bb97#64), (12, 0x1#64), (13, 0x1#64), (14, 0x8001bb20#64), (15, 0x1#64), (16, 0x8001b538#64), (17, 0x8001bb97#64), (18, 0x8001bb97#64), (19, 0x8001b538#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 97,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg054_00 chain
  [(0x8000efd4#64, 0x1059783#32),
   (0x8000efd8#64, 0xfd010113#32),
   (0x8000efdc#64, 0x68313#32),
   (0x8000efe0#64, 0x2113423#32),
   (0x8000efe4#64, 0x1007f693#32),
   (0x8000efe8#64, 0x58713#32),
   (0x8000efec#64, 0x60893#32),
   (0x8000eff0#64, 0x50813#32)]
    terminator ⟨0x8000eff4#64, 0x02069863#32, 0x63#8, 0x98#8, 0x06#8, 0x02#8, .br bop.BNE false, 13, 0, 0x0030#13, 0#21, 0#12⟩

def traceLds054_00 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts054_00 : ChainFacts (writeLog snapshotMem traceD054.log)
    (writeLog snapshotMem traceD054.log) traceD054.regs traceLds054_00 traceSeg054_00 := by
  have kind0 : (mkLine 0x8000efd4#64 0x1059783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000efd8#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000efdc#64 0x68313#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000efe0#64 0x2113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000efe4#64 0x1007f693#32).kind = MKind.andi := by decide
  have kind5 : (mkLine 0x8000efe8#64 0x58713#32).kind = MKind.addi := by decide
  have kind6 : (mkLine 0x8000efec#64 0x60893#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000eff0#64 0x50813#32).kind = MKind.addi := by decide
  simp only [traceSeg054_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run054_00 {c : Config} (h : TraceHolds traceD054 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD054_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg054_00 traceLds054_00 (by decide) facts054_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run054_00

#derive_case traceSeg054_01 chain
  [(0x8000eff8#64, 0xfffff6b7#32),
   (0x8000effc#64, 0xfff68693#32),
   (0x8000f000#64, 0x2813083#32),
   (0x8000f004#64, 0xd7f7b3#32),
   (0x8000f008#64, 0x1271583#32),
   (0x8000f00c#64, 0xf71823#32),
   (0x8000f010#64, 0x30693#32),
   (0x8000f014#64, 0x88613#32)]

def traceLds054_01 : List (List (BitVec 8)) :=
  [[0xc#8, 0xed#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8]]

theorem facts054_01 : ChainFacts (writeLog snapshotMem traceD054_01.log)
    (writeLog snapshotMem traceD054_01.log) traceD054_01.regs traceLds054_01 traceSeg054_01 := by
  have kind0 : (mkLine 0x8000eff8#64 0xfffff6b7#32).kind = MKind.lui := by decide
  have kind1 : (mkLine 0x8000effc#64 0xfff68693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000f000#64 0x2813083#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000f004#64 0xd7f7b3#32).kind = MKind.and := by decide
  have kind4 : (mkLine 0x8000f008#64 0x1271583#32).kind = MKind.lh := by decide
  have kind5 : (mkLine 0x8000f00c#64 0xf71823#32).kind = MKind.sh := by decide
  have kind6 : (mkLine 0x8000f010#64 0x30693#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x8000f014#64 0x88613#32).kind = MKind.addi := by decide
  simp only [traceSeg054_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run054_01 {c : Config} (h : TraceHolds traceD054_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD054_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg054_01 traceLds054_01 (by decide) facts054_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run054_01

#derive_case traceSeg054_02 chain
  [(0x8000f018#64, 0x80513#32),
   (0x8000f01c#64, 0x3010113#32)]
    terminator ⟨0x8000f020#64, 0x4dc0106f#32, 0x6f#8, 0x10#8, 0xc0#8, 0x4d#8, .j, 0, 0, 0#13, 0x0014dc#21, 0#12⟩

def traceLds054_02 : List (List (BitVec 8)) :=
  []

theorem facts054_02 : ChainFacts (writeLog snapshotMem traceD054_02.log)
    (writeLog snapshotMem traceD054_02.log) traceD054_02.regs traceLds054_02 traceSeg054_02 := by
  have kind0 : (mkLine 0x8000f018#64 0x80513#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000f01c#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg054_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00080513
    | exact DecodeTable.decode_03010113
    | exact DecodeTable.decode_4dc0106f
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run054_02 {c : Config} (h : TraceHolds traceD054_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD054_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg054_02 traceLds054_02 (by decide) facts054_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run054_02

#derive_case traceSeg054_03 chain
  [(0x800104fc#64, 0x58793#32),
   (0x80010500#64, 0xff010113#32),
   (0x80010504#64, 0x813023#32),
   (0x80010508#64, 0x60593#32),
   (0x8001050c#64, 0x50413#32),
   (0x80010510#64, 0x68613#32),
   (0x80010514#64, 0x78513#32),
   (0x80010518#64, 0x113423#32)]

def traceLds054_03 : List (List (BitVec 8)) :=
  []

theorem facts054_03 : ChainFacts (writeLog snapshotMem traceD054_03.log)
    (writeLog snapshotMem traceD054_03.log) traceD054_03.regs traceLds054_03 traceSeg054_03 := by
  have kind0 : (mkLine 0x800104fc#64 0x58793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80010500#64 0xff010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80010504#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80010508#64 0x60593#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8001050c#64 0x50413#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80010510#64 0x68613#32).kind = MKind.addi := by decide
  have kind6 : (mkLine 0x80010514#64 0x78513#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80010518#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg054_03, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run054_03 {c : Config} (h : TraceHolds traceD054_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD054_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg054_03 traceLds054_03 (by decide) facts054_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run054_03

#derive_case traceSeg054_04 chain
  [(0x8001051c#64, 0x4e01ac23#32)]

def traceLds054_04 : List (List (BitVec 8)) :=
  []

theorem facts054_04 : ChainFacts (writeLog snapshotMem traceD054_04.log)
    (writeLog snapshotMem traceD054_04.log) traceD054_04.regs traceLds054_04 traceSeg054_04 := by
  have kind0 : (mkLine 0x8001051c#64 0x4e01ac23#32).kind = MKind.sw := by decide
  simp only [traceSeg054_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_4e01ac23
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run054_04 {c : Config} (h : TraceHolds traceD054_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD055 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg054_04 traceLds054_04 (by decide) facts054_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run054_04
theorem run054 {c : Config} (h : TraceHolds traceD054 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD055 c' := by
  obtain ⟨c0, s0, h0⟩ := run054_00 h
  obtain ⟨c1, s1, h1⟩ := run054_01 h0
  obtain ⟨c2, s2, h2⟩ := run054_02 h1
  obtain ⟨c3, s3, h3⟩ := run054_03 h2
  obtain ⟨c4, s4, h4⟩ := run054_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run054
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts055 : TraceCallFacts traceD055 0xb1def0ef#32
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

theorem run055 {c : Config} (h : TraceHolds traceD055 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD056 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xb1def0ef#32 0x1efb1c#21 0xef#8 0xf0#8 0xde#8 0xb1#8 facts055 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run055
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg056 chain
  []
    terminator ⟨0x8000003c#64, 0x02060463#32, 0x63#8, 0x04#8, 0x06#8, 0x02#8, .br bop.BEQ false, 12, 0, 0x0028#13, 0#21, 0#12⟩ ;;
  [(0x80000040#64, 0x10100713#32),
   (0x80000044#64, 0xc586b3#32),
   (0x80000048#64, 0x3071713#32),
   (0x8000004c#64, 0x5c783#32),
   (0x80000050#64, 0x158593#32),
   (0x80000054#64, 0xe7e7b3#32),
   (0x80000058#64, 0x1b817#32)]

def traceLds056 : List (List (BitVec 8)) :=
  [[0xa#8]]

theorem facts056 : ChainFacts (writeLog snapshotMem traceD056.log)
    (writeLog snapshotMem traceD056.log) traceD056.regs traceLds056 traceSeg056 := by
  have kind0 : (mkLine 0x80000040#64 0x10100713#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80000044#64 0xc586b3#32).kind = MKind.add := by decide
  have kind2 : (mkLine 0x80000048#64 0x3071713#32).kind = MKind.slli := by decide
  have kind3 : (mkLine 0x8000004c#64 0x5c783#32).kind = MKind.lbu := by decide
  have kind4 : (mkLine 0x80000050#64 0x158593#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80000054#64 0xe7e7b3#32).kind = MKind.or := by decide
  have kind6 : (mkLine 0x80000058#64 0x1b817#32).kind = MKind.auipc := by decide
  simp only [traceSeg056, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run056 {c : Config} (h : TraceHolds traceD056 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD057 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg056 traceLds056 (by decide) facts056 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run056
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem run057 {c : Config} (h : TraceHolds traceD057 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD058 c' := by
  obtain ⟨c', hs, hp⟩ := h.putchar 0xa#8
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run057
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg058 chain
  []
    terminator ⟨0x80000060#64, 0xfed596e3#32, 0xe3#8, 0x96#8, 0xd5#8, 0xfe#8, .br bop.BNE false, 11, 13, 0x1fec#13, 0#21, 0#12⟩ ;;
  [(0x80000064#64, 0x60513#32)]
    terminator ⟨0x80000068#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds058 : List (List (BitVec 8)) :=
  []

theorem facts058 : ChainFacts (writeLog snapshotMem traceD058.log)
    (writeLog snapshotMem traceD058.log) traceD058.regs traceLds058 traceSeg058 := by
  have kind0 : (mkLine 0x80000064#64 0x60513#32).kind = MKind.addi := by decide
  simp only [traceSeg058, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00060513
    | exact DecodeTable.decode_fed596e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run058 {c : Config} (h : TraceHolds traceD058 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD059 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg058 traceLds058 (by decide) facts058 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run058
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg059 chain
  [(0x80010524#64, 0xfff00793#32)]
    terminator ⟨0x80010528#64, 0x00f50a63#32, 0x63#8, 0x0a#8, 0xf5#8, 0x00#8, .br bop.BEQ false, 10, 15, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8001052c#64, 0x813083#32),
   (0x80010530#64, 0x13403#32),
   (0x80010534#64, 0x1010113#32)]
    terminator ⟨0x80010538#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds059 : List (List (BitVec 8)) :=
  [[0xc#8, 0xed#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts059 : ChainFacts (writeLog snapshotMem traceD059.log)
    (writeLog snapshotMem traceD059.log) traceD059.regs traceLds059 traceSeg059 := by
  have kind0 : (mkLine 0x80010524#64 0xfff00793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8001052c#64 0x813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80010530#64 0x13403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80010534#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg059, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run059 {c : Config} (h : TraceHolds traceD059 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD060 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg059 traceLds059 (by decide) facts059 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run059
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg060 chain
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

def traceLds060 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xee#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts060 : ChainFacts (writeLog snapshotMem traceD060.log)
    (writeLog snapshotMem traceD060.log) traceD060.regs traceLds060 traceSeg060 := by
  have kind0 : (mkLine 0x8000ed0c#64 0x40a484bb#32).kind = MKind.subw := by decide
  have kind1 : (mkLine 0x8000ecec#64 0xa90933#32).kind = MKind.add := by decide
  have kind2 : (mkLine 0x8000ed4c#64 0x1813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ed50#64 0x1013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x8000ec9c#64 0x2813083#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000eca0#64 0x2013403#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x8000eca4#64 0x813983#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x8000eca8#64 0x513#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x8000ecac#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg060, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run060 {c : Config} (h : TraceHolds traceD060 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD061 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg060 traceLds060 (by decide) facts060 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run060
end Vsa.Sim.OutputAliasLoaded
