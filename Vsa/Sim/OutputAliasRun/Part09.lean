import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part12
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part17
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part26
import Vsa.Sim.DecodeTable.Batch01Part31
import Vsa.Sim.DecodeTable.Batch02Part07
import Vsa.Sim.DecodeTable.Batch02Part11
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part28
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch05Part32
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part18
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part08
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch07Part24
import Vsa.Sim.DecodeTable.Batch07Part29
import Vsa.Sim.DecodeTable.Batch08Part05
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch08Part21
import Vsa.Sim.DecodeTable.Batch08Part25
import Vsa.Sim.DecodeTable.Batch08Part28
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch08Part32
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part05
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch09Part12
import Vsa.Sim.DecodeTable.Batch09Part13
import Vsa.Sim.DecodeTable.Batch09Part20
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch10Part03
import Vsa.Sim.DecodeTable.Batch10Part19
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part06
import Vsa.Sim.DecodeTable.Batch12Part08
import Vsa.Sim.DecodeTable.Batch12Part13
import Vsa.Sim.DecodeTable.Batch13Part11
import Vsa.Sim.DecodeTable.Batch13Part25
import Vsa.Sim.DecodeTable.Batch15Part08
import Vsa.Sim.DecodeTable.Batch15Part17
import Vsa.Sim.DecodeTable.Batch15Part18
import Vsa.Sim.DecodeTable.Batch15Part29
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.DecodeTable.Batch17
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg181 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds181 : List (List (BitVec 8)) :=
  []

theorem facts181 : ChainFacts (writeLog snapshotMem traceD181.log)
    (writeLog snapshotMem traceD181.log) traceD181.regs traceLds181 traceSeg181 := by
  simp only [traceSeg181, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run181 {c : Config} (h : TraceHolds traceD181 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD182 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg181 traceLds181 (by decide) facts181 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 208 ++ (evalBlocks traceSeg181 (SegEvalState.init traceD181.regs traceLds181)).log = traceStores.take 208
  have hw : (evalBlocks traceSeg181 (SegEvalState.init traceD181.regs traceLds181)).log = (traceStores.drop 208).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run181
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg182 chain
  [(0x8000e77c#64, 0x813583#32),
   (0x8000e780#64, 0x2813083#32),
   (0x8000e784#64, 0x58513#32),
   (0x8000e788#64, 0x3010113#32)]
    terminator ⟨0x8000e78c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds182 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x2c#8, 0x63#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts182 : ChainFacts (writeLog snapshotMem traceD182.log)
    (writeLog snapshotMem traceD182.log) traceD182.regs traceLds182 traceSeg182 := by
  have kind0 : (mkLine 0x8000e77c#64 0x813583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000e780#64 0x2813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000e784#64 0x58513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000e788#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg182, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run182 {c : Config} (h : TraceHolds traceD182 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD183 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg182 traceLds182 (by decide) facts182 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 208 ++ (evalBlocks traceSeg182 (SegEvalState.init traceD182.regs traceLds182)).log = traceStores.take 208
  have hw : (evalBlocks traceSeg182 (SegEvalState.init traceD182.regs traceLds182)).log = (traceStores.drop 208).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run182
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg183 chain
  [(0x8000632c#64, 0xb042783#32),
   (0x80006330#64, 0x50713#32),
   (0x80006334#64, 0x17f793#32)]
    terminator ⟨0x80006338#64, 0x00079863#32, 0x63#8, 0x98#8, 0x07#8, 0x00#8, .br bop.BNE false, 15, 0, 0x0010#13, 0#21, 0#12⟩ ;;
  [(0x8000633c#64, 0x1045783#32),
   (0x80006340#64, 0x2007f793#32)]
    terminator ⟨0x80006344#64, 0x00078c63#32, 0x63#8, 0x8c#8, 0x07#8, 0x00#8, .br bop.BEQ true, 15, 0, 0x0018#13, 0#21, 0#12⟩ ;;
  [(0x8000635c#64, 0xa13023#32),
   (0x80006360#64, 0xa043503#32)]

def traceLds183 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa#8, 0x20#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts183 : ChainFacts (writeLog snapshotMem traceD183.log)
    (writeLog snapshotMem traceD183.log) traceD183.regs traceLds183 traceSeg183 := by
  have kind0 : (mkLine 0x8000632c#64 0xb042783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80006330#64 0x50713#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006334#64 0x17f793#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x8000633c#64 0x1045783#32).kind = MKind.lhu := by decide
  have kind4 : (mkLine 0x80006340#64 0x2007f793#32).kind = MKind.andi := by decide
  have kind5 : (mkLine 0x8000635c#64 0xa13023#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80006360#64 0xa043503#32).kind = MKind.ld := by decide
  simp only [traceSeg183, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run183 {c : Config} (h : TraceHolds traceD183 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD184 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg183 traceLds183 (by decide) facts183 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 208 ++ (evalBlocks traceSeg183 (SegEvalState.init traceD183.regs traceLds183)).log = traceStores.take 209
  have hw : (evalBlocks traceSeg183 (SegEvalState.init traceD183.regs traceLds183)).log = (traceStores.drop 208).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run183
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts184 : TraceCallFacts traceD184 0x495000ef#32
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

theorem run184 {c : Config} (h : TraceHolds traceD184 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD185 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x495000ef#32 0xc94#21 0xef#8 0x0#8 0x50#8 0x49#8 facts184 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run184
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg185 chain
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds185 : List (List (BitVec 8)) :=
  []

theorem facts185 : ChainFacts (writeLog snapshotMem traceD185.log)
    (writeLog snapshotMem traceD185.log) traceD185.regs traceLds185 traceSeg185 := by
  simp only [traceSeg185, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run185 {c : Config} (h : TraceHolds traceD185 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD186 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg185 traceLds185 (by decide) facts185 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 209 ++ (evalBlocks traceSeg185 (SegEvalState.init traceD185.regs traceLds185)).log = traceStores.take 209
  have hw : (evalBlocks traceSeg185 (SegEvalState.init traceD185.regs traceLds185)).log = (traceStores.drop 209).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run185
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg186 chain
  [(0x80006368#64, 0x13703#32),
   (0x8000636c#64, 0x1813083#32),
   (0x80006370#64, 0x1013403#32),
   (0x80006374#64, 0x70513#32),
   (0x80006378#64, 0x2010113#32)]
    terminator ⟨0x8000637c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds186 : List (List (BitVec 8)) :=
  [[0xa#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa4#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts186 : ChainFacts (writeLog snapshotMem traceD186.log)
    (writeLog snapshotMem traceD186.log) traceD186.regs traceLds186 traceSeg186 := by
  have kind0 : (mkLine 0x80006368#64 0x13703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000636c#64 0x1813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80006370#64 0x1013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80006374#64 0x70513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80006378#64 0x2010113#32).kind = MKind.addi := by decide
  simp only [traceSeg186, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run186 {c : Config} (h : TraceHolds traceD186 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD187 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg186 traceLds186 (by decide) facts186 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 209 ++ (evalBlocks traceSeg186 (SegEvalState.init traceD186.regs traceLds186)).log = traceStores.take 209
  have hw : (evalBlocks traceSeg186 (SegEvalState.init traceD186.regs traceLds186)).log = (traceStores.drop 209).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run186
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg187 chain
  [(0x80002fa4#64, 0x40513#32)]

def traceLds187 : List (List (BitVec 8)) :=
  []

theorem facts187 : ChainFacts (writeLog snapshotMem traceD187.log)
    (writeLog snapshotMem traceD187.log) traceD187.regs traceLds187 traceSeg187 := by
  have kind0 : (mkLine 0x80002fa4#64 0x40513#32).kind = MKind.addi := by decide
  simp only [traceSeg187, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00040513
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run187 {c : Config} (h : TraceHolds traceD187 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD188 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg187 traceLds187 (by decide) facts187 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 209 ++ (evalBlocks traceSeg187 (SegEvalState.init traceD187.regs traceLds187)).log = traceStores.take 209
  have hw : (evalBlocks traceSeg187 (SegEvalState.init traceD187.regs traceLds187)).log = (traceStores.drop 209).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run187
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts188 : TraceCallFacts traceD188 0x845ff0ef#32
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

theorem run188 {c : Config} (h : TraceHolds traceD188 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD189 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x845ff0ef#32 0x1ff844#21 0xef#8 0xf0#8 0x5f#8 0x84#8 facts188 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run188
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg189 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds189 : List (List (BitVec 8)) :=
  []

theorem facts189 : ChainFacts (writeLog snapshotMem traceD189.log)
    (writeLog snapshotMem traceD189.log) traceD189.regs traceLds189 traceSeg189 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg189, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run189 {c : Config} (h : TraceHolds traceD189 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD190 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg189 traceLds189 (by decide) facts189 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 209 ++ (evalBlocks traceSeg189 (SegEvalState.init traceD189.regs traceLds189)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg189 (SegEvalState.init traceD189.regs traceLds189)).log = (traceStores.drop 209).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run189
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg190 chain
  [(0x80002fac#64, 0x2813083#32),
   (0x80002fb0#64, 0x40513#32),
   (0x80002fb4#64, 0x2013403#32),
   (0x80002fb8#64, 0x3010113#32)]
    terminator ⟨0x80002fbc#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds190 : List (List (BitVec 8)) :=
  [[0xf8#8, 0x39#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts190 : ChainFacts (writeLog snapshotMem traceD190.log)
    (writeLog snapshotMem traceD190.log) traceD190.regs traceLds190 traceSeg190 := by
  have kind0 : (mkLine 0x80002fac#64 0x2813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002fb0#64 0x40513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002fb4#64 0x2013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002fb8#64 0x3010113#32).kind = MKind.addi := by decide
  simp only [traceSeg190, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run190 {c : Config} (h : TraceHolds traceD190 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD191 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg190 traceLds190 (by decide) facts190 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg190 (SegEvalState.init traceD190.regs traceLds190)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg190 (SegEvalState.init traceD190.regs traceLds190)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run190
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg191 chain
  [(0x800039f8#64, 0x3f813b83#32)]
    terminator ⟨0x800039fc#64, 0x9f1ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0x9f#8, .j, 0, 0, 0#13, 0x1ff9f0#21, 0#12⟩ ;;
  [(0x800033ec#64, 0x43813083#32),
   (0x800033f0#64, 0x43013403#32),
   (0x800033f4#64, 0x42013903#32),
   (0x800033f8#64, 0x48513#32),
   (0x800033fc#64, 0x42813483#32),
   (0x80003400#64, 0x44010113#32)]
    terminator ⟨0x80003404#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds191 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x84#8, 0x41#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x20#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa8#8, 0xfc#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts191 : ChainFacts (writeLog snapshotMem traceD191.log)
    (writeLog snapshotMem traceD191.log) traceD191.regs traceLds191 traceSeg191 := by
  have kind0 : (mkLine 0x800039f8#64 0x3f813b83#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800033ec#64 0x43813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800033f0#64 0x43013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800033f4#64 0x42013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800033f8#64 0x48513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800033fc#64 0x42813483#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80003400#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg191, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run191 {c : Config} (h : TraceHolds traceD191 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD192 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg191 traceLds191 (by decide) facts191 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg191 (SegEvalState.init traceD191.regs traceLds191)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg191 (SegEvalState.init traceD191.regs traceLds191)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run191
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg192 chain
  [(0x80004184#64, 0x513#32)]
    terminator ⟨0x80004188#64, 0xf15ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf1#8, .j, 0, 0, 0#13, 0x1fff14#21, 0#12⟩ ;;
  [(0x8000409c#64, 0xa813083#32),
   (0x800040a0#64, 0xa013403#32),
   (0x800040a4#64, 0x9813483#32),
   (0x800040a8#64, 0x9013903#32),
   (0x800040ac#64, 0x8813983#32),
   (0x800040b0#64, 0xb010113#32)]
    terminator ⟨0x800040b4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds192 : List (List (BitVec 8)) :=
  [[0x78#8, 0x44#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x8#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x40#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts192 : ChainFacts (writeLog snapshotMem traceD192.log)
    (writeLog snapshotMem traceD192.log) traceD192.regs traceLds192 traceSeg192 := by
  have kind0 : (mkLine 0x80004184#64 0x513#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x8000409c#64 0xa813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800040a0#64 0xa013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800040a4#64 0x9813483#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800040a8#64 0x9013903#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x800040ac#64 0x8813983#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x800040b0#64 0xb010113#32).kind = MKind.addi := by decide
  simp only [traceSeg192, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run192 {c : Config} (h : TraceHolds traceD192 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg192 traceLds192 (by decide) facts192 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg192 (SegEvalState.init traceD192.regs traceLds192)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg192 (SegEvalState.init traceD192.regs traceLds192)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run192
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD193_01 : TraceData :=
  { pc := 0x8000447c#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000008#64), (9, 0x82000040#64), (10, 0x0#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 211,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD193_02 : TraceData :=
  { pc := 0x80004484#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000008#64), (9, 0x82000040#64), (10, 0xffffffffffffffff#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 211,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD193_03 : TraceData :=
  { pc := 0x80004514#64,
    regs := [(1, 0x80004478#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000010#64), (9, 0x82000040#64), (10, 0xffffffffffffffff#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x82000010#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 211,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD193_04 : TraceData :=
  { pc := 0x80004524#64,
    regs := [(1, 0x800045ec#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0xffffffffffffffff#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0x3#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 211,
    out := #["\n", "\n"], payload := 0x0#4 }

def traceD193_05 : TraceData :=
  { pc := 0x80004534#64,
    regs := [(1, 0x800045ec#64), (2, 0x87fffc50#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x0#64), (10, 0x0#64), (11, 0xa#64), (12, 0x8001bb20#64), (13, 0x8001bb98#64), (14, 0xa#64), (15, 0x0#64), (16, 0x8001b058#64), (17, 0x8001bb97#64), (18, 0x0#64), (19, 0x0#64), (20, 0x0#64), (21, 0x0#64), (22, 0x0#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 211,
    out := #["\n", "\n"], payload := 0x0#4 }


#derive_case traceSeg193_00 chain
  []
    terminator ⟨0x80004478#64, 0x0d350463#32, 0x63#8, 0x04#8, 0x35#8, 0x0d#8, .br bop.BEQ false, 10, 19, 0x00c8#13, 0#21, 0#12⟩

def traceLds193_00 : List (List (BitVec 8)) :=
  []

theorem facts193_00 : ChainFacts (writeLog snapshotMem traceD193.log)
    (writeLog snapshotMem traceD193.log) traceD193.regs traceLds193_00 traceSeg193_00 := by
  simp only [traceSeg193_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0d350463
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_00 {c : Config} (h : TraceHolds traceD193 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_00 traceLds193_00 (by decide) facts193_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_00 (SegEvalState.init traceD193.regs traceLds193_00)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_00 (SegEvalState.init traceD193.regs traceLds193_00)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_00

#derive_case traceSeg193_01 chain
  [(0x8000447c#64, 0xfff5051b#32)]
    terminator ⟨0x80004480#64, 0x0eaa7263#32, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8, .br bop.BGEU false, 20, 10, 0x00e4#13, 0#21, 0#12⟩

def traceLds193_01 : List (List (BitVec 8)) :=
  []

theorem facts193_01 : ChainFacts (writeLog snapshotMem traceD193_01.log)
    (writeLog snapshotMem traceD193_01.log) traceD193_01.regs traceLds193_01 traceSeg193_01 := by
  have kind0 : (mkLine 0x8000447c#64 0xfff5051b#32).kind = MKind.addiw := by decide
  simp only [traceSeg193_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0eaa7263
    | exact DecodeTable.decode_fff5051b
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_01 {c : Config} (h : TraceHolds traceD193_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_01 traceLds193_01 (by decide) facts193_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_01 (SegEvalState.init traceD193_01.regs traceLds193_01)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_01 (SegEvalState.init traceD193_01.regs traceLds193_01)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_01

#derive_case traceSeg193_02 chain
  [(0x80004484#64, 0x840413#32)]
    terminator ⟨0x80004488#64, 0x09240663#32, 0x63#8, 0x06#8, 0x24#8, 0x09#8, .br bop.BEQ true, 8, 18, 0x008c#13, 0#21, 0#12⟩

def traceLds193_02 : List (List (BitVec 8)) :=
  []

theorem facts193_02 : ChainFacts (writeLog snapshotMem traceD193_02.log)
    (writeLog snapshotMem traceD193_02.log) traceD193_02.regs traceLds193_02 traceSeg193_02 := by
  have kind0 : (mkLine 0x80004484#64 0x840413#32).kind = MKind.addi := by decide
  simp only [traceSeg193_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00840413
    | exact DecodeTable.decode_09240663
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_02 {c : Config} (h : TraceHolds traceD193_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_02 traceLds193_02 (by decide) facts193_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_02 (SegEvalState.init traceD193_02.regs traceLds193_02)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_02 (SegEvalState.init traceD193_02.regs traceLds193_02)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_02

#derive_case traceSeg193_03 chain
  [(0x80004514#64, 0xa813083#32),
   (0x80004518#64, 0xa013403#32),
   (0x8000451c#64, 0x9813483#32),
   (0x80004520#64, 0x9013903#32)]

def traceLds193_03 : List (List (BitVec 8)) :=
  [[0xec#8, 0x45#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts193_03 : ChainFacts (writeLog snapshotMem traceD193_03.log)
    (writeLog snapshotMem traceD193_03.log) traceD193_03.regs traceLds193_03 traceSeg193_03 := by
  have kind0 : (mkLine 0x80004514#64 0xa813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004518#64 0xa013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000451c#64 0x9813483#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80004520#64 0x9013903#32).kind = MKind.ld := by decide
  simp only [traceSeg193_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_09013903
    | exact DecodeTable.decode_09813483
    | exact DecodeTable.decode_0a013403
    | exact DecodeTable.decode_0a813083
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_03 {c : Config} (h : TraceHolds traceD193_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_03 traceLds193_03 (by decide) facts193_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_03 (SegEvalState.init traceD193_03.regs traceLds193_03)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_03 (SegEvalState.init traceD193_03.regs traceLds193_03)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_03

#derive_case traceSeg193_04 chain
  [(0x80004524#64, 0x8813983#32),
   (0x80004528#64, 0x8013a03#32),
   (0x8000452c#64, 0x7013b03#32),
   (0x80004530#64, 0xa8513#32)]

def traceLds193_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts193_04 : ChainFacts (writeLog snapshotMem traceD193_04.log)
    (writeLog snapshotMem traceD193_04.log) traceD193_04.regs traceLds193_04 traceSeg193_04 := by
  have kind0 : (mkLine 0x80004524#64 0x8813983#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004528#64 0x8013a03#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000452c#64 0x7013b03#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80004530#64 0xa8513#32).kind = MKind.addi := by decide
  simp only [traceSeg193_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_000a8513
    | exact DecodeTable.decode_07013b03
    | exact DecodeTable.decode_08013a03
    | exact DecodeTable.decode_08813983
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_04 {c : Config} (h : TraceHolds traceD193_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD193_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_04 traceLds193_04 (by decide) facts193_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_04 (SegEvalState.init traceD193_04.regs traceLds193_04)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_04 (SegEvalState.init traceD193_04.regs traceLds193_04)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_04

#derive_case traceSeg193_05 chain
  [(0x80004534#64, 0x7813a83#32),
   (0x80004538#64, 0xb010113#32)]
    terminator ⟨0x8000453c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds193_05 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts193_05 : ChainFacts (writeLog snapshotMem traceD193_05.log)
    (writeLog snapshotMem traceD193_05.log) traceD193_05.regs traceLds193_05 traceSeg193_05 := by
  have kind0 : (mkLine 0x80004534#64 0x7813a83#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004538#64 0xb010113#32).kind = MKind.addi := by decide
  simp only [traceSeg193_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_07813a83
    | exact DecodeTable.decode_0b010113
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run193_05 {c : Config} (h : TraceHolds traceD193_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD194 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg193_05 traceLds193_05 (by decide) facts193_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg193_05 (SegEvalState.init traceD193_05.regs traceLds193_05)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg193_05 (SegEvalState.init traceD193_05.regs traceLds193_05)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run193_05
theorem run193 {c : Config} (h : TraceHolds traceD193 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD194 c' := by
  obtain ⟨c0, s0, h0⟩ := run193_00 h
  obtain ⟨c1, s1, h1⟩ := run193_01 h0
  obtain ⟨c2, s2, h2⟩ := run193_02 h1
  obtain ⟨c3, s3, h3⟩ := run193_03 h2
  obtain ⟨c4, s4, h4⟩ := run193_04 h3
  obtain ⟨c5, s5, h5⟩ := run193_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run193
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg194 chain
  []
    terminator ⟨0x800045ec#64, 0x00051a63#32, 0x63#8, 0x1a#8, 0x05#8, 0x00#8, .br bop.BNE false, 10, 0, 0x0014#13, 0#21, 0#12⟩ ;;
  [(0x800045f0#64, 0x2f813083#32),
   (0x800045f4#64, 0x2f013403#32),
   (0x800045f8#64, 0x30010113#32)]
    terminator ⟨0x800045fc#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds194 : List (List (BitVec 8)) :=
  [[0x38#8, 0x0#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts194 : ChainFacts (writeLog snapshotMem traceD194.log)
    (writeLog snapshotMem traceD194.log) traceD194.regs traceLds194 traceSeg194 := by
  have kind0 : (mkLine 0x800045f0#64 0x2f813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800045f4#64 0x2f013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800045f8#64 0x30010113#32).kind = MKind.addi := by decide
  simp only [traceSeg194, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00051a63
    | exact DecodeTable.decode_2f013403
    | exact DecodeTable.decode_2f813083
    | exact DecodeTable.decode_30010113
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run194 {c : Config} (h : TraceHolds traceD194 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD195 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg194 traceLds194 (by decide) facts194 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg194 (SegEvalState.init traceD194.regs traceLds194)).log = traceStores.take 211
  have hw : (evalBlocks traceSeg194 (SegEvalState.init traceD194.regs traceLds194)).log = (traceStores.drop 211).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run194
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg195 chain
  []
    terminator ⟨0x80000038#64, 0x72c0406f#32, 0x6f#8, 0x40#8, 0xc0#8, 0x72#8, .j, 0, 0, 0#13, 0x00472c#21, 0#12⟩ ;;
  [(0x80004764#64, 0xff010113#32),
   (0x80004768#64, 0x593#32),
   (0x8000476c#64, 0x813023#32),
   (0x80004770#64, 0x113423#32),
   (0x80004774#64, 0x50413#32)]

def traceLds195 : List (List (BitVec 8)) :=
  []

theorem facts195 : ChainFacts (writeLog snapshotMem traceD195.log)
    (writeLog snapshotMem traceD195.log) traceD195.regs traceLds195 traceSeg195 := by
  have kind0 : (mkLine 0x80004764#64 0xff010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80004768#64 0x593#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000476c#64 0x813023#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80004770#64 0x113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80004774#64 0x50413#32).kind = MKind.addi := by decide
  simp only [traceSeg195, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000593
    | exact DecodeTable.decode_00050413
    | exact DecodeTable.decode_00113423
    | exact DecodeTable.decode_00813023
    | exact DecodeTable.decode_ff010113
    | exact OutputAliasDecode.decode_72c0406f
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run195 {c : Config} (h : TraceHolds traceD195 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD196 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg195 traceLds195 (by decide) facts195 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 211 ++ (evalBlocks traceSeg195 (SegEvalState.init traceD195.regs traceLds195)).log = traceStores.take 213
  have hw : (evalBlocks traceSeg195 (SegEvalState.init traceD195.regs traceLds195)).log = (traceStores.drop 211).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run195
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts196 : TraceCallFacts traceD196 0x131020ef#32
    (instruction.JAL (0x2930#21, gprIdx 1)) 0xef#8 0x20#8 0x10#8 0x13#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_131020ef

theorem run196 {c : Config} (h : TraceHolds traceD196 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD197 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x131020ef#32 0x2930#21 0xef#8 0x20#8 0x10#8 0x13#8 facts196 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run196
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg197 chain
  [(0x800070a8#64, 0xfa010113#32),
   (0x800070ac#64, 0x1713c23#32),
   (0x800070b0#64, 0x46818b93#32),
   (0x800070b4#64, 0x3613023#32),
   (0x800070b8#64, 0x50b13#32),
   (0x800070bc#64, 0xbb503#32),
   (0x800070c0#64, 0x3413823#32),
   (0x800070c4#64, 0x4e818a13#32),
   (0x800070c8#64, 0x5213023#32),
   (0x800070cc#64, 0x1813823#32),
   (0x800070d0#64, 0x4113c23#32),
   (0x800070d4#64, 0x58c13#32)]

def traceLds197 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts197 : ChainFacts (writeLog snapshotMem traceD197.log)
    (writeLog snapshotMem traceD197.log) traceD197.regs traceLds197 traceSeg197 := by
  have kind0 : (mkLine 0x800070a8#64 0xfa010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x800070ac#64 0x1713c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x800070b0#64 0x46818b93#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800070b4#64 0x3613023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x800070b8#64 0x50b13#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800070bc#64 0xbb503#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x800070c0#64 0x3413823#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x800070c4#64 0x4e818a13#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x800070c8#64 0x5213023#32).kind = MKind.sd := by decide
  have kind9 : (mkLine 0x800070cc#64 0x1813823#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x800070d0#64 0x4113c23#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x800070d4#64 0x58c13#32).kind = MKind.addi := by decide
  simp only [traceSeg197, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050b13
    | exact DecodeTable.decode_00058c13
    | exact DecodeTable.decode_000bb503
    | exact DecodeTable.decode_01713c23
    | exact DecodeTable.decode_01813823
    | exact DecodeTable.decode_03413823
    | exact DecodeTable.decode_03613023
    | exact DecodeTable.decode_04113c23
    | exact DecodeTable.decode_05213023
    | exact DecodeTable.decode_46818b93
    | exact DecodeTable.decode_4e818a13
    | exact DecodeTable.decode_fa010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run197 {c : Config} (h : TraceHolds traceD197 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD198 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg197 traceLds197 (by decide) facts197 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 213 ++ (evalBlocks traceSeg197 (SegEvalState.init traceD197.regs traceLds197)).log = traceStores.take 219
  have hw : (evalBlocks traceSeg197 (SegEvalState.init traceD197.regs traceLds197)).log = (traceStores.drop 213).take 6 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run197
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts198 : TraceCallFacts traceD198 0xf09ff0ef#32
    (instruction.JAL (0x1fff08#21, gprIdx 1)) 0xef#8 0xf0#8 0x9f#8 0xf0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_f09ff0ef

theorem run198 {c : Config} (h : TraceHolds traceD198 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD199 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xf09ff0ef#32 0x1fff08#21 0xef#8 0xf0#8 0x9f#8 0xf0#8 facts198 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run198
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg199 chain
  []
    terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds199 : List (List (BitVec 8)) :=
  []

theorem facts199 : ChainFacts (writeLog snapshotMem traceD199.log)
    (writeLog snapshotMem traceD199.log) traceD199.regs traceLds199 traceSeg199 := by
  simp only [traceSeg199, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run199 {c : Config} (h : TraceHolds traceD199 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD200 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg199 traceLds199 (by decide) facts199 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 219 ++ (evalBlocks traceSeg199 (SegEvalState.init traceD199.regs traceLds199)).log = traceStores.take 219
  have hw : (evalBlocks traceSeg199 (SegEvalState.init traceD199.regs traceLds199)).log = (traceStores.drop 219).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run199
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg200 chain
  [(0x800070dc#64, 0xa3903#32)]
    terminator ⟨0x800070e0#64, 0x08090e63#32, 0x63#8, 0x0e#8, 0x09#8, 0x08#8, .br bop.BEQ true, 18, 0, 0x009c#13, 0#21, 0#12⟩ ;;
  [(0x8000717c#64, 0xbb503#32),
   (0x80007180#64, 0x5813083#32),
   (0x80007184#64, 0x4013903#32),
   (0x80007188#64, 0x3013a03#32),
   (0x8000718c#64, 0x2013b03#32),
   (0x80007190#64, 0x1813b83#32),
   (0x80007194#64, 0x1013c03#32),
   (0x80007198#64, 0x6010113#32)]
    terminator ⟨0x8000719c#64, 0xe5dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xe5#8, .j, 0, 0, 0#13, 0x1ffe5c#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds200 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x47#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts200 : ChainFacts (writeLog snapshotMem traceD200.log)
    (writeLog snapshotMem traceD200.log) traceD200.regs traceLds200 traceSeg200 := by
  have kind0 : (mkLine 0x800070dc#64 0xa3903#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000717c#64 0xbb503#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80007180#64 0x5813083#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80007184#64 0x4013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80007188#64 0x3013a03#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000718c#64 0x2013b03#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80007190#64 0x1813b83#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x80007194#64 0x1013c03#32).kind = MKind.ld := by decide
  have kind8 : (mkLine 0x80007198#64 0x6010113#32).kind = MKind.addi := by decide
  simp only [traceSeg200, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_000a3903
    | exact DecodeTable.decode_000bb503
    | exact DecodeTable.decode_01013c03
    | exact DecodeTable.decode_01813b83
    | exact DecodeTable.decode_02013b03
    | exact DecodeTable.decode_03013a03
    | exact DecodeTable.decode_04013903
    | exact DecodeTable.decode_05813083
    | exact DecodeTable.decode_06010113
    | exact DecodeTable.decode_08090e63
    | exact DecodeTable.decode_e5dff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run200 {c : Config} (h : TraceHolds traceD200 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD201 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg200 traceLds200 (by decide) facts200 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 219 ++ (evalBlocks traceSeg200 (SegEvalState.init traceD200.regs traceLds200)).log = traceStores.take 219
  have hw : (evalBlocks traceSeg200 (SegEvalState.init traceD200.regs traceLds200)).log = (traceStores.drop 219).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run200
end Vsa.Sim.OutputAliasLoaded
