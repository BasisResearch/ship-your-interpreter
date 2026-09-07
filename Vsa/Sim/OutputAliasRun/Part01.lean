import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part06
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch03Part29
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part28
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part16
import Vsa.Sim.DecodeTable.Batch05Part19
import Vsa.Sim.DecodeTable.Batch05Part20
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part03
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part29
import Vsa.Sim.DecodeTable.Batch07Part30
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part03
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part16
import Vsa.Sim.DecodeTable.Batch08Part18
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part29
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part14
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch10Part24
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch11Part06
import Vsa.Sim.DecodeTable.Batch11Part09
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part05
import Vsa.Sim.DecodeTable.Batch12Part22
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch13Part13
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part21
import Vsa.Sim.DecodeTable.Batch15Part27
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part05
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts021 : TraceCallFacts traceD021 0x238040ef#32
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

theorem run021 {c : Config} (h : TraceHolds traceD021 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD022 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x238040ef#32 0x4238#21 0xef#8 0x40#8 0x80#8 0x23#8 facts021 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run021
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg022 chain
  [(0x80006ea0#64, 0xb56733#32),
   (0x80006ea4#64, 0xfff00393#32),
   (0x80006ea8#64, 0x777713#32)]
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE false, 14, 0, 0x00d8#13, 0#21, 0#12⟩ ;;
  [(0x80006eb0#64, 0x14797#32),
   (0x80006eb4#64, 0xdd07b783#32),
   (0x80006eb8#64, 0x53603#32),
   (0x80006ebc#64, 0x5b683#32),
   (0x80006ec0#64, 0xf672b3#32),
   (0x80006ec4#64, 0xf66333#32),
   (0x80006ec8#64, 0xf282b3#32),
   (0x80006ecc#64, 0x62e2b3#32)]
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE true, 5, 7, 0x00dc#13, 0#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE false, 12, 13, 0x1fd8#13, 0#21, 0#12⟩ ;;
  [(0x80006fb0#64, 0x513#32)]
    terminator ⟨0x80006fb4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds022 : List (List (BitVec 8)) :=
  [[0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8]]

theorem facts022 : ChainFacts (writeLog snapshotMem traceD022.log)
    (writeLog snapshotMem traceD022.log) traceD022.regs traceLds022 traceSeg022 := by
  have kind0 : (mkLine 0x80006ea0#64 0xb56733#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x80006ea4#64 0xfff00393#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006ea8#64 0x777713#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x80006eb0#64 0x14797#32).kind = MKind.auipc := by decide
  have kind4 : (mkLine 0x80006eb4#64 0xdd07b783#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80006eb8#64 0x53603#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80006ebc#64 0x5b683#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x80006ec0#64 0xf672b3#32).kind = MKind.and := by decide
  have kind8 : (mkLine 0x80006ec4#64 0xf66333#32).kind = MKind.or := by decide
  have kind9 : (mkLine 0x80006ec8#64 0xf282b3#32).kind = MKind.add := by decide
  have kind10 : (mkLine 0x80006ecc#64 0x62e2b3#32).kind = MKind.or := by decide
  have kind11 : (mkLine 0x80006fb0#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg022, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00014797
    | exact DecodeTable.decode_00053603
    | exact DecodeTable.decode_0005b683
    | exact DecodeTable.decode_0062e2b3
    | exact DecodeTable.decode_00777713
    | exact DecodeTable.decode_00b56733
    | exact DecodeTable.decode_00f282b3
    | exact DecodeTable.decode_00f66333
    | exact DecodeTable.decode_00f672b3
    | exact DecodeTable.decode_0c071c63
    | exact DecodeTable.decode_0c729e63
    | exact DecodeTable.decode_dd07b783
    | exact DecodeTable.decode_fcd61ce3
    | exact DecodeTable.decode_fff00393
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run022 {c : Config} (h : TraceHolds traceD022 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD023 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg022 traceLds022 (by decide) facts022 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run022
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD023_01 : TraceData :=
  { pc := 0x80002c70#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x1#64), (9, 0x81000048#64), (10, 0x0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 49,
    out := #[], payload := 0x0#4 }

def traceD023_02 : TraceData :=
  { pc := 0x80002c90#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x1#64), (9, 0x81000048#64), (10, 0x1#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x5#64), (15, 0x81000098#64), (16, 0x8#64), (17, 0x0#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 50,
    out := #[], payload := 0x0#4 }

def traceD023_03 : TraceData :=
  { pc := 0x80002cb0#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x1#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x81000210#64), (15, 0x80002f7c#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 52,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg023_00 chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE false, 10, 0, 0x1fe8#13, 0#21, 0#12⟩

def traceLds023_00 : List (List (BitVec 8)) :=
  []

theorem facts023_00 : ChainFacts (writeLog snapshotMem traceD023.log)
    (writeLog snapshotMem traceD023.log) traceD023.regs traceLds023_00 traceSeg023_00 := by
  simp only [traceSeg023_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0514e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run023_00 {c : Config} (h : TraceHolds traceD023 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD023_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg023_00 traceLds023_00 (by decide) facts023_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run023_00

#derive_case traceSeg023_01 chain
  [(0x80002c70#64, 0x10a3783#32),
   (0x80002c74#64, 0x141713#32),
   (0x80002c78#64, 0x870733#32),
   (0x80002c7c#64, 0x371713#32),
   (0x80002c80#64, 0xe787b3#32),
   (0x80002c84#64, 0x7b703#32),
   (0x80002c88#64, 0x100513#32),
   (0x80002c8c#64, 0xeab023#32)]

def traceLds023_01 : List (List (BitVec 8)) :=
  [[0x80#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts023_01 : ChainFacts (writeLog snapshotMem traceD023_01.log)
    (writeLog snapshotMem traceD023_01.log) traceD023_01.regs traceLds023_01 traceSeg023_01 := by
  have kind0 : (mkLine 0x80002c70#64 0x10a3783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c74#64 0x141713#32).kind = MKind.slli := by decide
  have kind2 : (mkLine 0x80002c78#64 0x870733#32).kind = MKind.add := by decide
  have kind3 : (mkLine 0x80002c7c#64 0x371713#32).kind = MKind.slli := by decide
  have kind4 : (mkLine 0x80002c80#64 0xe787b3#32).kind = MKind.add := by decide
  have kind5 : (mkLine 0x80002c84#64 0x7b703#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80002c88#64 0x100513#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80002c8c#64 0xeab023#32).kind = MKind.sd := by decide
  simp only [traceSeg023_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0007b703
    | exact DecodeTable.decode_00100513
    | exact DecodeTable.decode_00141713
    | exact DecodeTable.decode_00371713
    | exact DecodeTable.decode_00870733
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_00eab023
    | exact DecodeTable.decode_010a3783
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run023_01 {c : Config} (h : TraceHolds traceD023_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD023_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg023_01 traceLds023_01 (by decide) facts023_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run023_01

#derive_case traceSeg023_02 chain
  [(0x80002c90#64, 0x87b703#32),
   (0x80002c94#64, 0xeab423#32),
   (0x80002c98#64, 0x107b783#32),
   (0x80002c9c#64, 0xfab823#32),
   (0x80002ca0#64, 0x3813083#32),
   (0x80002ca4#64, 0x3013403#32),
   (0x80002ca8#64, 0x2813483#32),
   (0x80002cac#64, 0x2013903#32)]

def traceLds023_02 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x44#8, 0x34#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0xf7#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts023_02 : ChainFacts (writeLog snapshotMem traceD023_02.log)
    (writeLog snapshotMem traceD023_02.log) traceD023_02.regs traceLds023_02 traceSeg023_02 := by
  have kind0 : (mkLine 0x80002c90#64 0x87b703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c94#64 0xeab423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002c98#64 0x107b783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002c9c#64 0xfab823#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80002ca0#64 0x3813083#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80002ca4#64 0x3013403#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80002ca8#64 0x2813483#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x80002cac#64 0x2013903#32).kind = MKind.ld := by decide
  simp only [traceSeg023_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0087b703
    | exact DecodeTable.decode_00eab423
    | exact DecodeTable.decode_00fab823
    | exact DecodeTable.decode_0107b783
    | exact DecodeTable.decode_02013903
    | exact DecodeTable.decode_02813483
    | exact DecodeTable.decode_03013403
    | exact DecodeTable.decode_03813083
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run023_02 {c : Config} (h : TraceHolds traceD023_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD023_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg023_02 traceLds023_02 (by decide) facts023_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run023_02

#derive_case traceSeg023_03 chain
  [(0x80002cb0#64, 0x1813983#32),
   (0x80002cb4#64, 0x1013a03#32),
   (0x80002cb8#64, 0x813a83#32),
   (0x80002cbc#64, 0x4010113#32)]
    terminator ⟨0x80002cc0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds023_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts023_03 : ChainFacts (writeLog snapshotMem traceD023_03.log)
    (writeLog snapshotMem traceD023_03.log) traceD023_03.regs traceLds023_03 traceSeg023_03 := by
  have kind0 : (mkLine 0x80002cb0#64 0x1813983#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002cb4#64 0x1013a03#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80002cb8#64 0x813a83#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002cbc#64 0x4010113#32).kind = MKind.addi := by decide
  simp only [traceSeg023_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00813a83
    | exact DecodeTable.decode_01013a03
    | exact DecodeTable.decode_01813983
    | exact DecodeTable.decode_04010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run023_03 {c : Config} (h : TraceHolds traceD023_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD024 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg023_03 traceLds023_03 (by decide) facts023_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run023_03
theorem run023 {c : Config} (h : TraceHolds traceD023 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD024 c' := by
  obtain ⟨c0, s0, h0⟩ := run023_00 h
  obtain ⟨c1, s1, h1⟩ := run023_01 h0
  obtain ⟨c2, s2, h2⟩ := run023_02 h1
  obtain ⟨c3, s3, h3⟩ := run023_03 h2
  exact ⟨c3, (((s0).trans s1).trans s2).trans s3, h3⟩

#print axioms run023
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg024 chain
  []
    terminator ⟨0x80003444#64, 0x32050ee3#32, 0xe3#8, 0x0e#8, 0x05#8, 0x32#8, .br bop.BEQ false, 10, 0, 0x0b3c#13, 0#21, 0#12⟩ ;;
  [(0x80003448#64, 0xf013683#32),
   (0x8000344c#64, 0xf813703#32),
   (0x80003450#64, 0x10013783#32),
   (0x80003454#64, 0x43813083#32),
   (0x80003458#64, 0x43013403#32),
   (0x8000345c#64, 0xd4b023#32),
   (0x80003460#64, 0xe4b423#32),
   (0x80003464#64, 0xf4b823#32),
   (0x80003468#64, 0x42013903#32),
   (0x8000346c#64, 0x48513#32),
   (0x80003470#64, 0x42813483#32),
   (0x80003474#64, 0x44010113#32)]
    terminator ⟨0x80003478#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds024 : List (List (BitVec 8)) :=
  [[0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0x31#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts024 : ChainFacts (writeLog snapshotMem traceD024.log)
    (writeLog snapshotMem traceD024.log) traceD024.regs traceLds024 traceSeg024 := by
  have kind0 : (mkLine 0x80003448#64 0xf013683#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000344c#64 0xf813703#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80003450#64 0x10013783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80003454#64 0x43813083#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80003458#64 0x43013403#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000345c#64 0xd4b023#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80003460#64 0xe4b423#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80003464#64 0xf4b823#32).kind = MKind.sd := by decide
  have kind8 : (mkLine 0x80003468#64 0x42013903#32).kind = MKind.ld := by decide
  have kind9 : (mkLine 0x8000346c#64 0x48513#32).kind = MKind.addi := by decide
  have kind10 : (mkLine 0x80003470#64 0x42813483#32).kind = MKind.ld := by decide
  have kind11 : (mkLine 0x80003474#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg024, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00d4b023
    | exact DecodeTable.decode_00e4b423
    | exact DecodeTable.decode_00f4b823
    | exact DecodeTable.decode_0f013683
    | exact DecodeTable.decode_0f813703
    | exact DecodeTable.decode_10013783
    | exact DecodeTable.decode_32050ee3
    | exact DecodeTable.decode_42013903
    | exact DecodeTable.decode_42813483
    | exact DecodeTable.decode_43013403
    | exact DecodeTable.decode_43813083
    | exact DecodeTable.decode_44010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run024 {c : Config} (h : TraceHolds traceD024 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD025 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg024 traceLds024 (by decide) facts024 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run024
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD025_01 : TraceData :=
  { pc := 0x800031cc#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x5#64), (14, 0x20#64), (15, 0x0#64), (16, 0x8#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 55,
    out := #[], payload := 0x0#4 }

def traceD025_02 : TraceData :=
  { pc := 0x80003254#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x81000000#64), (14, 0x20#64), (15, 0x0#64), (16, 0x0#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 56,
    out := #[], payload := 0x0#4 }

def traceD025_03 : TraceData :=
  { pc := 0x80003274#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x0#64), (12, 0x6e6c746e697270#64), (13, 0x81000210#64), (14, 0x5#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 59,
    out := #[], payload := 0x0#4 }

def traceD025_04 : TraceData :=
  { pc := 0x800039e0#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x0#64), (12, 0x5#64), (13, 0x81000210#64), (14, 0x5#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 59,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg025_00 chain
  [(0x800031c0#64, 0x1842783#32),
   (0x800031c4#64, 0x2000713#32)]
    terminator ⟨0x800031c8#64, 0x5ef744e3#32, 0xe3#8, 0x44#8, 0xf7#8, 0x5e#8, .br bop.BLT false, 14, 15, 0x0de8#13, 0#21, 0#12⟩

def traceLds025_00 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts025_00 : ChainFacts (writeLog snapshotMem traceD025.log)
    (writeLog snapshotMem traceD025.log) traceD025.regs traceLds025_00 traceSeg025_00 := by
  have kind0 : (mkLine 0x800031c0#64 0x1842783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x800031c4#64 0x2000713#32).kind = MKind.addi := by decide
  simp only [traceSeg025_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01842783
    | exact DecodeTable.decode_02000713
    | exact DecodeTable.decode_5ef744e3
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run025_00 {c : Config} (h : TraceHolds traceD025 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD025_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg025_00 traceLds025_00 (by decide) facts025_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run025_00

#derive_case traceSeg025_01 chain
  [(0x800031cc#64, 0x3f713c23#32),
   (0x800031d0#64, 0x13683#32),
   (0x800031d4#64, 0x813#32)]
    terminator ⟨0x800031d8#64, 0x06f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x06#8, .br bop.BGE true, 0, 15, 0x007c#13, 0#21, 0#12⟩

def traceLds025_01 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts025_01 : ChainFacts (writeLog snapshotMem traceD025_01.log)
    (writeLog snapshotMem traceD025_01.log) traceD025_01.regs traceLds025_01 traceSeg025_01 := by
  have kind0 : (mkLine 0x800031cc#64 0x3f713c23#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x800031d0#64 0x13683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800031d4#64 0x813#32).kind = MKind.addi := by decide
  simp only [traceSeg025_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000813
    | exact DecodeTable.decode_00013683
    | exact DecodeTable.decode_06f05e63
    | exact DecodeTable.decode_3f713c23
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run025_01 {c : Config} (h : TraceHolds traceD025_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD025_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg025_01 traceLds025_01 (by decide) facts025_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run025_01

#derive_case traceSeg025_02 chain
  [(0x80003254#64, 0x6013703#32),
   (0x80003258#64, 0x6813683#32),
   (0x8000325c#64, 0x7013803#32),
   (0x80003260#64, 0x442583#32),
   (0x80003264#64, 0x6e13c23#32),
   (0x80003268#64, 0x6012703#32),
   (0x8000326c#64, 0x8d13023#32),
   (0x80003270#64, 0x9013423#32)]

def traceLds025_02 : List (List (BitVec 8)) :=
  [[0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x5#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts025_02 : ChainFacts (writeLog snapshotMem traceD025_02.log)
    (writeLog snapshotMem traceD025_02.log) traceD025_02.regs traceLds025_02 traceSeg025_02 := by
  have kind0 : (mkLine 0x80003254#64 0x6013703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80003258#64 0x6813683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000325c#64 0x7013803#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80003260#64 0x442583#32).kind = MKind.lw := by decide
  have kind4 : (mkLine 0x80003264#64 0x6e13c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003268#64 0x6012703#32).kind = MKind.lw := by decide
  have kind6 : (mkLine 0x8000326c#64 0x8d13023#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80003270#64 0x9013423#32).kind = MKind.sd := by decide
  simp only [traceSeg025_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00442583
    | exact DecodeTable.decode_06012703
    | exact DecodeTable.decode_06013703
    | exact DecodeTable.decode_06813683
    | exact DecodeTable.decode_06e13c23
    | exact DecodeTable.decode_07013803
    | exact DecodeTable.decode_08d13023
    | exact DecodeTable.decode_09013423
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run025_02 {c : Config} (h : TraceHolds traceD025_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD025_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg025_02 traceLds025_02 (by decide) facts025_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run025_02

#derive_case traceSeg025_03 chain
  [(0x80003274#64, 0x500613#32),
   (0x80003278#64, 0x58b93#32)]
    terminator ⟨0x8000327c#64, 0x76c70263#32, 0x63#8, 0x02#8, 0xc7#8, 0x76#8, .br bop.BEQ true, 14, 12, 0x0764#13, 0#21, 0#12⟩

def traceLds025_03 : List (List (BitVec 8)) :=
  []

theorem facts025_03 : ChainFacts (writeLog snapshotMem traceD025_03.log)
    (writeLog snapshotMem traceD025_03.log) traceD025_03.regs traceLds025_03 traceSeg025_03 := by
  have kind0 : (mkLine 0x80003274#64 0x500613#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003278#64 0x58b93#32).kind = MKind.addi := by decide
  simp only [traceSeg025_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058b93
    | exact DecodeTable.decode_00500613
    | exact DecodeTable.decode_76c70263
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run025_03 {c : Config} (h : TraceHolds traceD025_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD025_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg025_03 traceLds025_03 (by decide) facts025_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run025_03

#derive_case traceSeg025_04 chain
  [(0x800039e0#64, 0x58713#32),
   (0x800039e4#64, 0x78613#32),
   (0x800039e8#64, 0x90593#32),
   (0x800039ec#64, 0xf010693#32),
   (0x800039f0#64, 0x48513#32)]

def traceLds025_04 : List (List (BitVec 8)) :=
  []

theorem facts025_04 : ChainFacts (writeLog snapshotMem traceD025_04.log)
    (writeLog snapshotMem traceD025_04.log) traceD025_04.regs traceLds025_04 traceSeg025_04 := by
  have kind0 : (mkLine 0x800039e0#64 0x58713#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x800039e4#64 0x78613#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800039e8#64 0x90593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800039ec#64 0xf010693#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x800039f0#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg025_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00058713
    | exact DecodeTable.decode_00078613
    | exact DecodeTable.decode_00090593
    | exact DecodeTable.decode_0f010693
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run025_04 {c : Config} (h : TraceHolds traceD025_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD026 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg025_04 traceLds025_04 (by decide) facts025_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run025_04
theorem run025 {c : Config} (h : TraceHolds traceD025 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD026 c' := by
  obtain ⟨c0, s0, h0⟩ := run025_00 h
  obtain ⟨c1, s1, h1⟩ := run025_01 h0
  obtain ⟨c2, s2, h2⟩ := run025_02 h1
  obtain ⟨c3, s3, h3⟩ := run025_03 h2
  obtain ⟨c4, s4, h4⟩ := run025_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run025
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts026 : TraceCallFacts traceD026 0x800e7#32
    (instruction.JALR (0x0#12, gprIdx 16, gprIdx 1)) 0xe7#8 0x0#8 0x8#8 0x0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_000800e7

theorem run026 {c : Config} (h : TraceHolds traceD026 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD027 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x800e7#32 0x0#12 16 0x80002f7c#64
    0xe7#8 0x0#8 0x8#8 0x0#8 facts026
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run026
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg027 chain
  [(0x80002f7c#64, 0xfd010113#32),
   (0x80002f80#64, 0x2813023#32),
   (0x80002f84#64, 0x50413#32),
   (0x80002f88#64, 0x10513#32),
   (0x80002f8c#64, 0x2113423#32)]

def traceLds027 : List (List (BitVec 8)) :=
  []

theorem facts027 : ChainFacts (writeLog snapshotMem traceD027.log)
    (writeLog snapshotMem traceD027.log) traceD027.regs traceLds027 traceSeg027 := by
  have kind0 : (mkLine 0x80002f7c#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002f80#64 0x2813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002f84#64 0x50413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80002f88#64 0x10513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80002f8c#64 0x2113423#32).kind = MKind.sd := by decide
  simp only [traceSeg027, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00010513
    | exact DecodeTable.decode_00050413
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_02813023
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run027 {c : Config} (h : TraceHolds traceD027 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD028 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg027 traceLds027 (by decide) facts027 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run027
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts028 : TraceCallFacts traceD028 0xf45ff0ef#32
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

theorem run028 {c : Config} (h : TraceHolds traceD028 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD029 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xf45ff0ef#32 0x1fff44#21 0xef#8 0xf0#8 0x5f#8 0xf4#8 facts028 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run028
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg029 chain
  [(0x80002ed4#64, 0xfb010113#32),
   (0x80002ed8#64, 0x3413023#32),
   (0x80002edc#64, 0x4113423#32),
   (0x80002ee0#64, 0x50a13#32)]
    terminator ⟨0x80002ee4#64, 0x06c05e63#32, 0x63#8, 0x5e#8, 0xc0#8, 0x06#8, .br bop.BGE true, 0, 12, 0x007c#13, 0#21, 0#12⟩ ;;
  [(0x80002f60#64, 0xa0513#32)]

def traceLds029 : List (List (BitVec 8)) :=
  []

theorem facts029 : ChainFacts (writeLog snapshotMem traceD029.log)
    (writeLog snapshotMem traceD029.log) traceD029.regs traceLds029 traceSeg029 := by
  have kind0 : (mkLine 0x80002ed4#64 0xfb010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002ed8#64 0x3413023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002edc#64 0x4113423#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80002ee0#64 0x50a13#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80002f60#64 0xa0513#32).kind = MKind.addi := by decide
  simp only [traceSeg029, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run029 {c : Config} (h : TraceHolds traceD029 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD030 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg029 traceLds029 (by decide) facts029 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run029
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts030 : TraceCallFacts traceD030 0x889ff0ef#32
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

theorem run030 {c : Config} (h : TraceHolds traceD030 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD031 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x889ff0ef#32 0x1ff888#21 0xef#8 0xf0#8 0x9f#8 0x88#8 facts030 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run030
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg031 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds031 : List (List (BitVec 8)) :=
  []

theorem facts031 : ChainFacts (writeLog snapshotMem traceD031.log)
    (writeLog snapshotMem traceD031.log) traceD031.regs traceLds031 traceSeg031 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg031, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run031 {c : Config} (h : TraceHolds traceD031 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD032 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg031 traceLds031 (by decide) facts031 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run031
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg032 chain
  [(0x80002f68#64, 0x4813083#32),
   (0x80002f6c#64, 0xa0513#32),
   (0x80002f70#64, 0x2013a03#32),
   (0x80002f74#64, 0x5010113#32)]
    terminator ⟨0x80002f78#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds032 : List (List (BitVec 8)) :=
  [[0x94#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts032 : ChainFacts (writeLog snapshotMem traceD032.log)
    (writeLog snapshotMem traceD032.log) traceD032.regs traceLds032 traceSeg032 := by
  have kind0 : (mkLine 0x80002f68#64 0x4813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002f6c#64 0xa0513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002f70#64 0x2013a03#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002f74#64 0x5010113#32).kind = MKind.addi := by decide
  simp only [traceSeg032, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run032 {c : Config} (h : TraceHolds traceD032 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD033 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg032 traceLds032 (by decide) facts032 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run032
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg033 chain
  [(0x80002f94#64, 0x4601b783#32),
   (0x80002f98#64, 0xa00513#32),
   (0x80002f9c#64, 0x107b583#32)]

def traceLds033 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts033 : ChainFacts (writeLog snapshotMem traceD033.log)
    (writeLog snapshotMem traceD033.log) traceD033.regs traceLds033 traceSeg033 := by
  have kind0 : (mkLine 0x80002f94#64 0x4601b783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002f98#64 0xa00513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002f9c#64 0x107b583#32).kind = MKind.ld := by decide
  simp only [traceSeg033, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00a00513
    | exact DecodeTable.decode_0107b583
    | exact DecodeTable.decode_4601b783
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run033 {c : Config} (h : TraceHolds traceD033 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD034 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg033 traceLds033 (by decide) facts033 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run033
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts034 : TraceCallFacts traceD034 0x340030ef#32
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

theorem run034 {c : Config} (h : TraceHolds traceD034 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD035 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x340030ef#32 0x3340#21 0xef#8 0x30#8 0x0#8 0x34#8 facts034 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run034
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD035_01 : TraceData :=
  { pc := 0x800062fc#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x8001b538#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 67,
    out := #[], payload := 0x0#4 }

def traceD035_02 : TraceData :=
  { pc := 0x80006304#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x80005d2c#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 67,
    out := #[], payload := 0x0#4 }

def traceD035_03 : TraceData :=
  { pc := 0x80006310#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 67,
    out := #[], payload := 0x0#4 }

def traceD035_04 : TraceData :=
  { pc := 0x80006380#64,
    regs := [(1, 0x80002fa4#64), (2, 0x87fff710#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x8001bb20#64), (9, 0x87fffbb0#64), (10, 0xa#64), (11, 0x8001bb20#64), (12, 0x0#64), (13, 0xa#64), (14, 0x8001b538#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x0#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 67,
    out := #[], payload := 0x0#4 }


#derive_case traceSeg035_00 chain
  [(0x800062e0#64, 0x4601b703#32),
   (0x800062e4#64, 0xfe010113#32),
   (0x800062e8#64, 0x813823#32),
   (0x800062ec#64, 0x113c23#32),
   (0x800062f0#64, 0x50693#32),
   (0x800062f4#64, 0x58413#32)]
    terminator ⟨0x800062f8#64, 0x00070663#32, 0x63#8, 0x06#8, 0x07#8, 0x00#8, .br bop.BEQ false, 14, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds035_00 : List (List (BitVec 8)) :=
  [[0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts035_00 : ChainFacts (writeLog snapshotMem traceD035.log)
    (writeLog snapshotMem traceD035.log) traceD035.regs traceLds035_00 traceSeg035_00 := by
  have kind0 : (mkLine 0x800062e0#64 0x4601b703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800062e4#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800062e8#64 0x813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x800062ec#64 0x113c23#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x800062f0#64 0x50693#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800062f4#64 0x58413#32).kind = MKind.addi := by decide
  simp only [traceSeg035_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run035_00 {c : Config} (h : TraceHolds traceD035 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD035_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg035_00 traceLds035_00 (by decide) facts035_00 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run035_00

#derive_case traceSeg035_01 chain
  [(0x800062fc#64, 0x4873783#32)]
    terminator ⟨0x80006300#64, 0x08078e63#32, 0x63#8, 0x8e#8, 0x07#8, 0x08#8, .br bop.BEQ false, 15, 0, 0x009c#13, 0#21, 0#12⟩

def traceLds035_01 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts035_01 : ChainFacts (writeLog snapshotMem traceD035_01.log)
    (writeLog snapshotMem traceD035_01.log) traceD035_01.regs traceLds035_01 traceSeg035_01 := by
  have kind0 : (mkLine 0x800062fc#64 0x4873783#32).kind = MKind.ld := by decide
  simp only [traceSeg035_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04873783
    | exact DecodeTable.decode_08078e63
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run035_01 {c : Config} (h : TraceHolds traceD035_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD035_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg035_01 traceLds035_01 (by decide) facts035_01 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run035_01

#derive_case traceSeg035_02 chain
  [(0x80006304#64, 0xb042783#32),
   (0x80006308#64, 0x17f793#32)]
    terminator ⟨0x8000630c#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩

def traceLds035_02 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts035_02 : ChainFacts (writeLog snapshotMem traceD035_02.log)
    (writeLog snapshotMem traceD035_02.log) traceD035_02.regs traceLds035_02 traceSeg035_02 := by
  have kind0 : (mkLine 0x80006304#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80006308#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg035_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00079863
    | exact DecodeTable.decode_0017f793
    | exact DecodeTable.decode_0b042783
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run035_02 {c : Config} (h : TraceHolds traceD035_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD035_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg035_02 traceLds035_02 (by decide) facts035_02 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run035_02

#derive_case traceSeg035_03 chain
  [(0x80006310#64, 0x1045783#32),
   (0x80006314#64, 0x2007f793#32)]
    terminator ⟨0x80006318#64, 0x06078463#32, 0x63#8, 0x84#8, 0x07#8, 0x06#8, .br bop.BEQ true, 15, 0, 0x0068#13, 0#21, 0#12⟩

def traceLds035_03 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8]]

theorem facts035_03 : ChainFacts (writeLog snapshotMem traceD035_03.log)
    (writeLog snapshotMem traceD035_03.log) traceD035_03.regs traceLds035_03 traceSeg035_03 := by
  have kind0 : (mkLine 0x80006310#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind1 : (mkLine 0x80006314#64 0x2007f793#32).kind = MKind.andi := by decide
  simp only [traceSeg035_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_06078463
    | exact DecodeTable.decode_2007f793
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run035_03 {c : Config} (h : TraceHolds traceD035_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD035_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg035_03 traceLds035_03 (by decide) facts035_03 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run035_03

#derive_case traceSeg035_04 chain
  [(0x80006380#64, 0xa043503#32),
   (0x80006384#64, 0xd13423#32),
   (0x80006388#64, 0xe13023#32)]

def traceLds035_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts035_04 : ChainFacts (writeLog snapshotMem traceD035_04.log)
    (writeLog snapshotMem traceD035_04.log) traceD035_04.regs traceLds035_04 traceSeg035_04 := by
  have kind0 : (mkLine 0x80006380#64 0xa043503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80006384#64 0xd13423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80006388#64 0xe13023#32).kind = MKind.sd := by decide
  simp only [traceSeg035_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00d13423
    | exact DecodeTable.decode_00e13023
    | exact DecodeTable.decode_0a043503
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run035_04 {c : Config} (h : TraceHolds traceD035_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD036 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg035_04 traceLds035_04 (by decide) facts035_04 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run035_04
theorem run035 {c : Config} (h : TraceHolds traceD035 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD036 c' := by
  obtain ⟨c0, s0, h0⟩ := run035_00 h
  obtain ⟨c1, s1, h1⟩ := run035_01 h0
  obtain ⟨c2, s2, h2⟩ := run035_02 h1
  obtain ⟨c3, s3, h3⟩ := run035_03 h2
  obtain ⟨c4, s4, h4⟩ := run035_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run035
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts036 : TraceCallFacts traceD036 0x455000ef#32
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

theorem run036 {c : Config} (h : TraceHolds traceD036 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD037 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x455000ef#32 0xc54#21 0xef#8 0x0#8 0x50#8 0x45#8 facts036 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run036
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg037 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds037 : List (List (BitVec 8)) :=
  []

theorem facts037 : ChainFacts (writeLog snapshotMem traceD037.log)
    (writeLog snapshotMem traceD037.log) traceD037.regs traceLds037 traceSeg037 := by
  simp only [traceSeg037, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run037 {c : Config} (h : TraceHolds traceD037 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD038 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg037 traceLds037 (by decide) facts037 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run037
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg038 chain
  [(0x80006390#64, 0x813683#32),
   (0x80006394#64, 0x13703#32)]
    terminator ⟨0x80006398#64, 0xf85ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf8#8, .j, 0, 0, 0#13, 0x1fff84#21, 0#12⟩ ;;
  [(0x8000631c#64, 0x70513#32),
   (0x80006320#64, 0x68593#32),
   (0x80006324#64, 0x40613#32)]

def traceLds038 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x38#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts038 : ChainFacts (writeLog snapshotMem traceD038.log)
    (writeLog snapshotMem traceD038.log) traceD038.regs traceLds038 traceSeg038 := by
  have kind0 : (mkLine 0x80006390#64 0x813683#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80006394#64 0x13703#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000631c#64 0x70513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006320#64 0x68593#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80006324#64 0x40613#32).kind = MKind.addi := by decide
  simp only [traceSeg038, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run038 {c : Config} (h : TraceHolds traceD038 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD039 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg038 traceLds038 (by decide) facts038 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run038
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts039 : TraceCallFacts traceD039 0x37c080ef#32
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

theorem run039 {c : Config} (h : TraceHolds traceD039 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD040 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x37c080ef#32 0x837c#21 0xef#8 0x80#8 0xc0#8 0x37#8 facts039 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run039
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg040 chain
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

def traceLds040 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts040 : ChainFacts (writeLog snapshotMem traceD040.log)
    (writeLog snapshotMem traceD040.log) traceD040.regs traceLds040 traceSeg040 := by
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
  simp only [traceSeg040, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run040 {c : Config} (h : TraceHolds traceD040 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD041 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg040 traceLds040 (by decide) facts040 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run040
end Vsa.Sim.OutputAliasLoaded
