import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part05
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part13
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch07Part32
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch12Part12
import Vsa.Sim.DecodeTable.Batch14Part26
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part26
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg241 chain
  [(0x80000098#64, 0x513#32)]
    terminator ⟨0x8000009c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds241 : List (List (BitVec 8)) :=
  []

theorem facts241 : ChainFacts (writeLog snapshotMem traceD241.log)
    (writeLog snapshotMem traceD241.log) traceD241.regs traceLds241 traceSeg241 := by
  have kind0 : (mkLine 0x80000098#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg241, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run241 {c : Config} (h : TraceHolds traceD241 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD242 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg241 traceLds241 (by decide) facts241 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 254 ++ (evalBlocks traceSeg241 (SegEvalState.init traceD241.regs traceLds241)).log = traceStores.take 254
  have hw : (evalBlocks traceSeg241 (SegEvalState.init traceD241.regs traceLds241)).log = (traceStores.drop 254).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run241
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg242 chain
  [(0x80010284#64, 0xfff00793#32)]
    terminator ⟨0x80010288#64, 0x00f50a63#32, 0x63#8, 0x0a#8, 0xf5#8, 0x00#8, .br bop.BEQ false, 10, 15, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x8001028c#64, 0x813083#32),
   (0x80010290#64, 0x13403#32),
   (0x80010294#64, 0x1010113#32)]
    terminator ⟨0x80010298#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds242 : List (List (BitVec 8)) :=
  [[0x60#8, 0xea#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts242 : ChainFacts (writeLog snapshotMem traceD242.log)
    (writeLog snapshotMem traceD242.log) traceD242.regs traceLds242 traceSeg242 := by
  have kind0 : (mkLine 0x80010284#64 0xfff00793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8001028c#64 0x813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80010290#64 0x13403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80010294#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg242, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run242 {c : Config} (h : TraceHolds traceD242 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD243 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg242 traceLds242 (by decide) facts242 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 254 ++ (evalBlocks traceSeg242 (SegEvalState.init traceD242.regs traceLds242)).log = traceStores.take 254
  have hw : (evalBlocks traceSeg242 (SegEvalState.init traceD242.regs traceLds242)).log = (traceStores.drop 254).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run242
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg243 chain
  []
    terminator ⟨0x8000ea60#64, 0x0a054063#32, 0x63#8, 0x40#8, 0x05#8, 0x0a#8, .br bop.BLT false, 10, 0, 0x00a0#13, 0#21, 0#12⟩ ;;
  [(0x8000ea64#64, 0x1045783#32),
   (0x8000ea68#64, 0x807f793#32)]
    terminator ⟨0x8000ea6c#64, 0x0a079263#32, 0x63#8, 0x92#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00a4#13, 0#21, 0#12⟩ ;;
  [(0x8000ea70#64, 0x5843583#32)]
    terminator ⟨0x8000ea74#64, 0x00058c63#32, 0x63#8, 0x8c#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x8000ea8c#64, 0x7843583#32)]
    terminator ⟨0x8000ea90#64, 0x00058863#32, 0x63#8, 0x88#8, 0x05#8, 0x00#8, .br bop.BEQ true, 11, 0, 0x0010#13, 0#21, 0#12⟩

def traceLds243 : List (List (BitVec 8)) :=
  [[0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts243 : ChainFacts (writeLog snapshotMem traceD243.log)
    (writeLog snapshotMem traceD243.log) traceD243.regs traceLds243 traceSeg243 := by
  have kind0 : (mkLine 0x8000ea64#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind1 : (mkLine 0x8000ea68#64 0x807f793#32).kind = MKind.andi := by decide
  have kind2 : (mkLine 0x8000ea70#64 0x5843583#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000ea8c#64 0x7843583#32).kind = MKind.ld := by decide
  simp only [traceSeg243, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run243 {c : Config} (h : TraceHolds traceD243 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD244 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg243 traceLds243 (by decide) facts243 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 254 ++ (evalBlocks traceSeg243 (SegEvalState.init traceD243.regs traceLds243)).log = traceStores.take 254
  have hw : (evalBlocks traceSeg243 (SegEvalState.init traceD243.regs traceLds243)).log = (traceStores.drop 254).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run243
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts244 : TraceCallFacts traceD244 0xe80f70ef#32
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

theorem run244 {c : Config} (h : TraceHolds traceD244 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD245 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe80f70ef#32 0x1f7680#21 0xef#8 0x70#8 0xf#8 0xe8#8 facts244 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run244
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg245 chain
  [(0x80006120#64, 0x4e018513#32)]
    terminator ⟨0x80006124#64, 0x6bd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6b#8, .j, 0, 0, 0#13, 0x000ebc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds245 : List (List (BitVec 8)) :=
  []

theorem facts245 : ChainFacts (writeLog snapshotMem traceD245.log)
    (writeLog snapshotMem traceD245.log) traceD245.regs traceLds245 traceSeg245 := by
  have kind0 : (mkLine 0x80006120#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg245, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6bd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run245 {c : Config} (h : TraceHolds traceD245 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD246 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg245 traceLds245 (by decide) facts245 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 254 ++ (evalBlocks traceSeg245 (SegEvalState.init traceD245.regs traceLds245)).log = traceStores.take 254
  have hw : (evalBlocks traceSeg245 (SegEvalState.init traceD245.regs traceLds245)).log = (traceStores.drop 254).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run245
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg246 chain
  [(0x8000eaa4#64, 0xb042783#32),
   (0x8000eaa8#64, 0x41823#32),
   (0x8000eaac#64, 0x17f793#32)]
    terminator ⟨0x8000eab0#64, 0x0a078463#32, 0x63#8, 0x84#8, 0x07#8, 0x0a#8, .br bop.BEQ true, 15, 0, 0x00a8#13, 0#21, 0#12⟩ ;;
  [(0x8000eb58#64, 0xa043503#32)]

def traceLds246 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts246 : ChainFacts (writeLog snapshotMem traceD246.log)
    (writeLog snapshotMem traceD246.log) traceD246.regs traceLds246 traceSeg246 := by
  have kind0 : (mkLine 0x8000eaa4#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000eaa8#64 0x41823#32).kind = MKind.sh := by decide
  have kind2 : (mkLine 0x8000eaac#64 0x17f793#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000eb58#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg246, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run246 {c : Config} (h : TraceHolds traceD246 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD247 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg246 traceLds246 (by decide) facts246 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 254 ++ (evalBlocks traceSeg246 (SegEvalState.init traceD246.regs traceLds246)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg246 (SegEvalState.init traceD246.regs traceLds246)).log = (traceStores.drop 254).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run246
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts247 : TraceCallFacts traceD247 0xc9cf80ef#32
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

theorem run247 {c : Config} (h : TraceHolds traceD247 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD248 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xc9cf80ef#32 0x1f849c#21 0xef#8 0x80#8 0xcf#8 0xc9#8 facts247 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run247
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg248 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds248 : List (List (BitVec 8)) :=
  []

theorem facts248 : ChainFacts (writeLog snapshotMem traceD248.log)
    (writeLog snapshotMem traceD248.log) traceD248.regs traceLds248 traceSeg248 := by
  simp only [traceSeg248, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run248 {c : Config} (h : TraceHolds traceD248 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD249 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg248 traceLds248 (by decide) facts248 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg248 (SegEvalState.init traceD248.regs traceLds248)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg248 (SegEvalState.init traceD248.regs traceLds248)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run248
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg249 chain
  []
    terminator ⟨0x8000eb60#64, 0xf55ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf5#8, .j, 0, 0, 0#13, 0x1fff54#21, 0#12⟩ ;;
  [(0x8000eab4#64, 0xa043503#32)]

def traceLds249 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts249 : ChainFacts (writeLog snapshotMem traceD249.log)
    (writeLog snapshotMem traceD249.log) traceD249.regs traceLds249 traceSeg249 := by
  have kind0 : (mkLine 0x8000eab4#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg249, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | exact DecodeTable.decode_f55ff06f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run249 {c : Config} (h : TraceHolds traceD249 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD250 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg249 traceLds249 (by decide) facts249 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg249 (SegEvalState.init traceD249.regs traceLds249)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg249 (SegEvalState.init traceD249.regs traceLds249)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run249
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts250 : TraceCallFacts traceD250 0xd20f80ef#32
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

theorem run250 {c : Config} (h : TraceHolds traceD250 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD251 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xd20f80ef#32 0x1f8520#21 0xef#8 0x80#8 0xf#8 0xd2#8 facts250 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run250
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg251 chain
  []
    terminator ⟨0x80006fd8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds251 : List (List (BitVec 8)) :=
  []

theorem facts251 : ChainFacts (writeLog snapshotMem traceD251.log)
    (writeLog snapshotMem traceD251.log) traceD251.regs traceLds251 traceSeg251 := by
  simp only [traceSeg251, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run251 {c : Config} (h : TraceHolds traceD251 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD252 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg251 traceLds251 (by decide) facts251 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg251 (SegEvalState.init traceD251.regs traceLds251)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg251 (SegEvalState.init traceD251.regs traceLds251)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run251
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts252 : TraceCallFacts traceD252 0xe6cf70ef#32
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

theorem run252 {c : Config} (h : TraceHolds traceD252 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD253 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe6cf70ef#32 0x1f766c#21 0xef#8 0x70#8 0xcf#8 0xe6#8 facts252 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run252
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg253 chain
  [(0x80006128#64, 0x4e018513#32)]
    terminator ⟨0x8000612c#64, 0x6cd0006f#32, 0x6f#8, 0x00#8, 0xd0#8, 0x6c#8, .j, 0, 0, 0#13, 0x000ecc#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds253 : List (List (BitVec 8)) :=
  []

theorem facts253 : ChainFacts (writeLog snapshotMem traceD253.log)
    (writeLog snapshotMem traceD253.log) traceD253.regs traceLds253 traceSeg253 := by
  have kind0 : (mkLine 0x80006128#64 0x4e018513#32).kind = MKind.addi := by decide
  simp only [traceSeg253, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_4e018513
    | exact OutputAliasDecode.decode_6cd0006f
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run253 {c : Config} (h : TraceHolds traceD253 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD254 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg253 traceLds253 (by decide) facts253 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg253 (SegEvalState.init traceD253.regs traceLds253)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg253 (SegEvalState.init traceD253.regs traceLds253)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run253
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg254 chain
  [(0x8000eac0#64, 0x1813083#32),
   (0x8000eac4#64, 0x1013403#32),
   (0x8000eac8#64, 0x813483#32),
   (0x8000eacc#64, 0x90513#32),
   (0x8000ead0#64, 0x13903#32),
   (0x8000ead4#64, 0x2010113#32)]
    terminator ⟨0x8000ead8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds254 : List (List (BitVec 8)) :=
  [[0xf0#8, 0xe3#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x90#8, 0xbc#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0xb5#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts254 : ChainFacts (writeLog snapshotMem traceD254.log)
    (writeLog snapshotMem traceD254.log) traceD254.regs traceLds254 traceSeg254 := by
  have kind0 : (mkLine 0x8000eac0#64 0x1813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000eac4#64 0x1013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000eac8#64 0x813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000eacc#64 0x90513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000ead0#64 0x13903#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000ead4#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg254, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run254 {c : Config} (h : TraceHolds traceD254 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD255 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg254 traceLds254 (by decide) facts254 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg254 (SegEvalState.init traceD254.regs traceLds254)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg254 (SegEvalState.init traceD254.regs traceLds254)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run254
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD255_01 : TraceData :=
  { pc := 0x8000e3d4#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 255,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD255_02 : TraceData :=
  { pc := 0x8000e3dc#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffffa0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001bc90#64), (10, 0x0#64), (11, 0x0#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x12#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 255,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg255_00 chain
  [(0x8000e3f0#64, 0x1656b33#32),
   (0x8000e3f4#64, 0xb0b1b#32),
   (0x8000e3f8#64, 0xb840413#32)]
    terminator ⟨0x8000e3fc#64, 0xfc941ce3#32, 0xe3#8, 0x1c#8, 0x94#8, 0xfc#8, .br bop.BNE true, 8, 9, 0x1fd8#13, 0#21, 0#12⟩

def traceLds255_00 : List (List (BitVec 8)) :=
  []

theorem facts255_00 : ChainFacts (writeLog snapshotMem traceD255.log)
    (writeLog snapshotMem traceD255.log) traceD255.regs traceLds255_00 traceSeg255_00 := by
  have kind0 : (mkLine 0x8000e3f0#64 0x1656b33#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x8000e3f4#64 0xb0b1b#32).kind = MKind.addiw := by decide
  have kind2 : (mkLine 0x8000e3f8#64 0xb840413#32).kind = MKind.addi := by decide
  simp only [traceSeg255_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run255_00 {c : Config} (h : TraceHolds traceD255 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD255_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg255_00 traceLds255_00 (by decide) facts255_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg255_00 (SegEvalState.init traceD255.regs traceLds255_00)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg255_00 (SegEvalState.init traceD255.regs traceLds255_00)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run255_00

#derive_case traceSeg255_01 chain
  [(0x8000e3d4#64, 0x1045783#32)]
    terminator ⟨0x8000e3d8#64, 0x02fbf063#32, 0x63#8, 0xf0#8, 0xfb#8, 0x02#8, .br bop.BGEU false, 23, 15, 0x0020#13, 0#21, 0#12⟩

def traceLds255_01 : List (List (BitVec 8)) :=
  [[0x12#8, 0x0#8]]

theorem facts255_01 : ChainFacts (writeLog snapshotMem traceD255_01.log)
    (writeLog snapshotMem traceD255_01.log) traceD255_01.regs traceLds255_01 traceSeg255_01 := by
  have kind0 : (mkLine 0x8000e3d4#64 0x1045783#32).kind = MKind.lhu := by decide
  simp only [traceSeg255_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01045783
    | exact DecodeTable.decode_02fbf063
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run255_01 {c : Config} (h : TraceHolds traceD255_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD255_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg255_01 traceLds255_01 (by decide) facts255_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg255_01 (SegEvalState.init traceD255_01.regs traceLds255_01)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg255_01 (SegEvalState.init traceD255_01.regs traceLds255_01)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run255_01

#derive_case traceSeg255_02 chain
  [(0x8000e3dc#64, 0x1241783#32),
   (0x8000e3e0#64, 0x40593#32),
   (0x8000e3e4#64, 0xa0513#32)]
    terminator ⟨0x8000e3e8#64, 0x01378863#32, 0x63#8, 0x88#8, 0x37#8, 0x01#8, .br bop.BEQ false, 15, 19, 0x0010#13, 0#21, 0#12⟩

def traceLds255_02 : List (List (BitVec 8)) :=
  [[0x2#8, 0x0#8]]

theorem facts255_02 : ChainFacts (writeLog snapshotMem traceD255_02.log)
    (writeLog snapshotMem traceD255_02.log) traceD255_02.regs traceLds255_02 traceSeg255_02 := by
  have kind0 : (mkLine 0x8000e3dc#64 0x1241783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000e3e0#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000e3e4#64 0xa0513#32).kind = MKind.addi := by decide
  simp only [traceSeg255_02, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run255_02 {c : Config} (h : TraceHolds traceD255_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD256 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg255_02 traceLds255_02 (by decide) facts255_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg255_02 (SegEvalState.init traceD255_02.regs traceLds255_02)).log = traceStores.take 255
  have hw : (evalBlocks traceSeg255_02 (SegEvalState.init traceD255_02.regs traceLds255_02)).log = (traceStores.drop 255).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run255_02
theorem run255 {c : Config} (h : TraceHolds traceD255 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD256 c' := by
  obtain ⟨c0, s0, h0⟩ := run255_00 h
  obtain ⟨c1, s1, h1⟩ := run255_01 h0
  obtain ⟨c2, s2, h2⟩ := run255_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run255
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts256 : TraceCallFacts traceD256 0xa80e7#32
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

theorem run256 {c : Config} (h : TraceHolds traceD256 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0xa80e7#32 0x0#12 21 0x8000e9f8#64
    0xe7#8 0x80#8 0xa#8 0x0#8 facts256
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run256
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD257_01 : TraceData :=
  { pc := 0x8000ea08#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001bc90#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x2#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 257,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD257_02 : TraceData :=
  { pc := 0x8000ea1c#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x2#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 259,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD257_03 : TraceData :=
  { pc := 0x8000ea24#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x2#64), (15, 0x80005d2c#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 259,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD257_04 : TraceData :=
  { pc := 0x8000ea34#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x12#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 259,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD257_05 : TraceData :=
  { pc := 0x8000eb28#64,
    regs := [(1, 0x8000e3f0#64), (2, 0x87ffff80#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x8001bbd8#64), (9, 0x8001b538#64), (10, 0x8001b538#64), (11, 0x8001bbd8#64), (12, 0x8001b520#64), (13, 0x0#64), (14, 0x0#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x8001b520#64), (19, 0xffffffffffffffff#64), (20, 0x8001b538#64), (21, 0x8000e9f8#64), (22, 0x0#64), (23, 0x1#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 259,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg257_00 chain
  [(0x8000e9f8#64, 0xfe010113#32),
   (0x8000e9fc#64, 0x113c23#32),
   (0x8000ea00#64, 0x1213023#32)]
    terminator ⟨0x8000ea04#64, 0x0e058263#32, 0x63#8, 0x82#8, 0x05#8, 0x0e#8, .br bop.BEQ false, 11, 0, 0x00e4#13, 0#21, 0#12⟩

def traceLds257_00 : List (List (BitVec 8)) :=
  []

theorem facts257_00 : ChainFacts (writeLog snapshotMem traceD257.log)
    (writeLog snapshotMem traceD257.log) traceD257.regs traceLds257_00 traceSeg257_00 := by
  have kind0 : (mkLine 0x8000e9f8#64 0xfe010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000e9fc#64 0x113c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea00#64 0x1213023#32).kind = MKind.sd := by decide
  simp only [traceSeg257_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run257_00 {c : Config} (h : TraceHolds traceD257 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_00 traceLds257_00 (by decide) facts257_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 255 ++ (evalBlocks traceSeg257_00 (SegEvalState.init traceD257.regs traceLds257_00)).log = traceStores.take 257
  have hw : (evalBlocks traceSeg257_00 (SegEvalState.init traceD257.regs traceLds257_00)).log = (traceStores.drop 255).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_00

#derive_case traceSeg257_01 chain
  [(0x8000ea08#64, 0x813823#32),
   (0x8000ea0c#64, 0x913423#32),
   (0x8000ea10#64, 0x58413#32),
   (0x8000ea14#64, 0x50493#32)]
    terminator ⟨0x8000ea18#64, 0x00050663#32, 0x63#8, 0x06#8, 0x05#8, 0x00#8, .br bop.BEQ false, 10, 0, 0x000c#13, 0#21, 0#12⟩

def traceLds257_01 : List (List (BitVec 8)) :=
  []

theorem facts257_01 : ChainFacts (writeLog snapshotMem traceD257_01.log)
    (writeLog snapshotMem traceD257_01.log) traceD257_01.regs traceLds257_01 traceSeg257_01 := by
  have kind0 : (mkLine 0x8000ea08#64 0x813823#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x8000ea0c#64 0x913423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x8000ea10#64 0x58413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000ea14#64 0x50493#32).kind = MKind.addi := by decide
  simp only [traceSeg257_01, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run257_01 {c : Config} (h : TraceHolds traceD257_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_01 traceLds257_01 (by decide) facts257_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 257 ++ (evalBlocks traceSeg257_01 (SegEvalState.init traceD257_01.regs traceLds257_01)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg257_01 (SegEvalState.init traceD257_01.regs traceLds257_01)).log = (traceStores.drop 257).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_01

#derive_case traceSeg257_02 chain
  [(0x8000ea1c#64, 0x4853783#32)]
    terminator ⟨0x8000ea20#64, 0x10078063#32, 0x63#8, 0x80#8, 0x07#8, 0x10#8, .br bop.BEQ false, 15, 0, 0x0100#13, 0#21, 0#12⟩

def traceLds257_02 : List (List (BitVec 8)) :=
  [[0x2c#8, 0x5d#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts257_02 : ChainFacts (writeLog snapshotMem traceD257_02.log)
    (writeLog snapshotMem traceD257_02.log) traceD257_02.regs traceLds257_02 traceSeg257_02 := by
  have kind0 : (mkLine 0x8000ea1c#64 0x4853783#32).kind = MKind.ld := by decide
  simp only [traceSeg257_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_04853783
    | exact OutputAliasDecode.decode_10078063
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run257_02 {c : Config} (h : TraceHolds traceD257_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_02 traceLds257_02 (by decide) facts257_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg257_02 (SegEvalState.init traceD257_02.regs traceLds257_02)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg257_02 (SegEvalState.init traceD257_02.regs traceLds257_02)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_02

#derive_case traceSeg257_03 chain
  [(0x8000ea24#64, 0xb042783#32),
   (0x8000ea28#64, 0x1041703#32),
   (0x8000ea2c#64, 0x17f793#32)]
    terminator ⟨0x8000ea30#64, 0x0a079663#32, 0x63#8, 0x96#8, 0x07#8, 0x0a#8, .br bop.BNE false, 15, 0, 0x00ac#13, 0#21, 0#12⟩

def traceLds257_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x12#8, 0x0#8]]

theorem facts257_03 : ChainFacts (writeLog snapshotMem traceD257_03.log)
    (writeLog snapshotMem traceD257_03.log) traceD257_03.regs traceLds257_03 traceSeg257_03 := by
  have kind0 : (mkLine 0x8000ea24#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x8000ea28#64 0x1041703#32).kind = MKind.lh := by decide
  have kind2 : (mkLine 0x8000ea2c#64 0x17f793#32).kind = MKind.andi := by decide
  simp only [traceSeg257_03, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run257_03 {c : Config} (h : TraceHolds traceD257_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_03 traceLds257_03 (by decide) facts257_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg257_03 (SegEvalState.init traceD257_03.regs traceLds257_03)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg257_03 (SegEvalState.init traceD257_03.regs traceLds257_03)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_03

#derive_case traceSeg257_04 chain
  [(0x8000ea34#64, 0x20077713#32)]
    terminator ⟨0x8000ea38#64, 0x0e070863#32, 0x63#8, 0x08#8, 0x07#8, 0x0e#8, .br bop.BEQ true, 14, 0, 0x00f0#13, 0#21, 0#12⟩

def traceLds257_04 : List (List (BitVec 8)) :=
  []

theorem facts257_04 : ChainFacts (writeLog snapshotMem traceD257_04.log)
    (writeLog snapshotMem traceD257_04.log) traceD257_04.regs traceLds257_04 traceSeg257_04 := by
  have kind0 : (mkLine 0x8000ea34#64 0x20077713#32).kind = MKind.andi := by decide
  simp only [traceSeg257_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_20077713
    | exact OutputAliasDecode.decode_0e070863
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run257_04 {c : Config} (h : TraceHolds traceD257_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD257_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_04 traceLds257_04 (by decide) facts257_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg257_04 (SegEvalState.init traceD257_04.regs traceLds257_04)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg257_04 (SegEvalState.init traceD257_04.regs traceLds257_04)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_04

#derive_case traceSeg257_05 chain
  [(0x8000eb28#64, 0xa043503#32)]

def traceLds257_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts257_05 : ChainFacts (writeLog snapshotMem traceD257_05.log)
    (writeLog snapshotMem traceD257_05.log) traceD257_05.regs traceLds257_05 traceSeg257_05 := by
  have kind0 : (mkLine 0x8000eb28#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg257_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0a043503
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run257_05 {c : Config} (h : TraceHolds traceD257_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD258 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg257_05 traceLds257_05 (by decide) facts257_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg257_05 (SegEvalState.init traceD257_05.regs traceLds257_05)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg257_05 (SegEvalState.init traceD257_05.regs traceLds257_05)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run257_05
theorem run257 {c : Config} (h : TraceHolds traceD257 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD258 c' := by
  obtain ⟨c0, s0, h0⟩ := run257_00 h
  obtain ⟨c1, s1, h1⟩ := run257_01 h0
  obtain ⟨c2, s2, h2⟩ := run257_02 h1
  obtain ⟨c3, s3, h3⟩ := run257_03 h2
  obtain ⟨c4, s4, h4⟩ := run257_04 h3
  obtain ⟨c5, s5, h5⟩ := run257_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run257
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts258 : TraceCallFacts traceD258 0xcb4f80ef#32
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

theorem run258 {c : Config} (h : TraceHolds traceD258 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD259 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xcb4f80ef#32 0x1f84b4#21 0xef#8 0x80#8 0x4f#8 0xcb#8 facts258 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run258
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg259 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds259 : List (List (BitVec 8)) :=
  []

theorem facts259 : ChainFacts (writeLog snapshotMem traceD259.log)
    (writeLog snapshotMem traceD259.log) traceD259.regs traceLds259 traceSeg259 := by
  simp only [traceSeg259, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run259 {c : Config} (h : TraceHolds traceD259 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD260 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg259 traceLds259 (by decide) facts259 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg259 (SegEvalState.init traceD259.regs traceLds259)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg259 (SegEvalState.init traceD259.regs traceLds259)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run259
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg260 chain
  [(0x8000eb30#64, 0x1041783#32)]
    terminator ⟨0x8000eb34#64, 0xf00794e3#32, 0xe3#8, 0x94#8, 0x07#8, 0xf0#8, .br bop.BNE true, 15, 0, 0x1f08#13, 0#21, 0#12⟩ ;;
  [(0x8000ea3c#64, 0x40593#32),
   (0x8000ea40#64, 0x48513#32)]

def traceLds260 : List (List (BitVec 8)) :=
  [[0x12#8, 0x0#8]]

theorem facts260 : ChainFacts (writeLog snapshotMem traceD260.log)
    (writeLog snapshotMem traceD260.log) traceD260.regs traceLds260 traceSeg260 := by
  have kind0 : (mkLine 0x8000eb30#64 0x1041783#32).kind = MKind.lh := by decide
  have kind1 : (mkLine 0x8000ea3c#64 0x40593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000ea40#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg260, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run260 {c : Config} (h : TraceHolds traceD260 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD261 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg260 traceLds260 (by decide) facts260 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 259 ++ (evalBlocks traceSeg260 (SegEvalState.init traceD260.regs traceLds260)).log = traceStores.take 259
  have hw : (evalBlocks traceSeg260 (SegEvalState.init traceD260.regs traceLds260)).log = (traceStores.drop 259).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run260
end Vsa.Sim.OutputAliasLoaded
