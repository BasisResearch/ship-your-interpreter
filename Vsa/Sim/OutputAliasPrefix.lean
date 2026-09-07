import Vsa.Sim.OutputAliasTrace
import Vsa.Sim.SegEvalSound
import Vsa.Sim.DeriveCase
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch08Part23
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch15Part22

/-! The first fourteen concrete instructions of the closed alias snapshot.
The certificate stops immediately before the setjmp JAL. -/

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim.OutputAliasLoaded

#derive_case firstSegment chain
  [(0x800043ec#64, 0xf5010113#32), -- addi sp,sp,-176
   (0x800043f0#64, 0x00a13023#32), -- sd a0,0(sp)
   (0x800043f4#64, 0x01050513#32), -- addi a0,a0,16
   (0x800043f8#64, 0x0a113423#32), -- sd ra,168(sp)
   (0x800043fc#64, 0x0a813023#32), -- sd s0,160(sp)
   (0x80004400#64, 0x08913c23#32), -- sd s1,152(sp)
   (0x80004404#64, 0x09213823#32), -- sd s2,144(sp)
   (0x80004408#64, 0x09313423#32), -- sd s3,136(sp)
   (0x8000440c#64, 0x09413023#32), -- sd s4,128(sp)
   (0x80004410#64, 0x07513c23#32), -- sd s5,120(sp)
   (0x80004414#64, 0x07613823#32), -- sd s6,112(sp)
   (0x80004418#64, 0x00b13c23#32), -- sd a1,24(sp)
   (0x8000441c#64, 0x00c13823#32), -- sd a2,16(sp)
   (0x80004420#64, 0x00d13423#32)] -- sd a3,8(sp)

/-- Every general-purpose register present in the explicit initial state. -/
def firstSegmentL : GRegs :=
  [(1, 0x800045ec#64), (2, 0x87fffd00#64), (3, 0x8001b510#64),
   (4, 0#64), (5, 0#64), (6, 0#64), (7, 0#64), (8, 0#64), (9, 0#64),
   (10, 0x87fffe10#64), (11, 0x82000000#64), (12, 2#64),
   (13, 0#64), (14, 0#64), (15, 0#64), (16, 0#64), (17, 0#64),
   (18, 0#64), (19, 0#64), (20, 0#64), (21, 0#64), (22, 0#64),
   (23, 0#64), (24, 0#64), (25, 0#64), (26, 0#64), (27, 0#64),
   (28, 0#64), (29, 0#64), (30, 0#64), (31, 0#64)]

def firstSegmentEval : SegEvalState :=
  evalBlocks firstSegment (SegEvalState.init firstSegmentL [])

/-- Twelve actual stores, in instruction order. -/
def firstSegmentLog : List WEntry :=
  [(0x87fffc50, 8, 0x87fffe10#64), (0x87fffcf8, 8, 0x800045ec#64),
   (0x87fffcf0, 8, 0#64), (0x87fffce8, 8, 0#64), (0x87fffce0, 8, 0#64),
   (0x87fffcd8, 8, 0#64), (0x87fffcd0, 8, 0#64), (0x87fffcc8, 8, 0#64),
   (0x87fffcc0, 8, 0#64), (0x87fffc68, 8, 0x82000000#64),
   (0x87fffc60, 8, 2#64), (0x87fffc58, 8, 0#64)]

theorem firstSegment_log : firstSegmentEval.log = firstSegmentLog := by rfl

theorem firstSegment_regs : GHolds snapshotConfig.σ firstSegmentL := by
  simp [firstSegmentL, GHolds, gprGet, snapshotConfig, physicalConfig,
    physicalState, LayoutInstance.spEntry, LayoutInstance.gpEntry,
    LayoutInstance.interpObject]

/-- Code bytes come from the finite snapshot backend. Decodes come from the
fixed ISA table. All store windows are closed numeric facts. -/
theorem firstSegment_facts :
    ChainFacts snapshotMem snapshotMem firstSegmentL [] firstSegment := by
  simp only [firstSegment, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, TermPins, TermFactsO, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | (rw [snapshot_lookup]; decide)
    | exact DecodeTable.decode_f5010113
    | exact DecodeTable.decode_00a13023
    | exact DecodeTable.decode_01050513
    | exact DecodeTable.decode_0a113423
    | exact DecodeTable.decode_0a813023
    | exact DecodeTable.decode_08913c23
    | exact DecodeTable.decode_09213823
    | exact DecodeTable.decode_09313423
    | exact DecodeTable.decode_09413023
    | exact DecodeTable.decode_07513c23
    | exact DecodeTable.decode_07613823
    | exact DecodeTable.decode_00b13c23
    | exact DecodeTable.decode_00c13823
    | exact DecodeTable.decode_00d13423
    | decide

structure FirstSegmentPost (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  steps : c.steps = 14
  pc : c.σ.regs.get? Register.PC = some 0x80004424#64
  mem : c.σ.mem = writeLog snapshotMem firstSegmentLog
  regs : GHolds c.σ firstSegmentEval.regs
  sp : gprGet c.σ 2 = some 0x87fffc50#64
  a0 : gprGet c.σ 10 = some 0x87fffe20#64
  minstret : ∃ n, c.σ.regs.get? Register.minstret = some n
  out : c.σ.sailOutput = #[]
  payload : c.σ.regs.get? Register.htif_payload_writes = some (0#4)
  tohost : c.σ.regs.get? Register.htif_tohost = some (0#64)

/-- Closed machine execution from the admitted concrete snapshot. -/
theorem snapshot_firstSegment :
    ∃ c : Config, Steps snapshotConfig c ∧ FirstSegmentPost c := by
  obtain ⟨σ', i', hs, hi, hG, hm, ho, hp, hmi, hr, hframe⟩ :=
    segEval_sound firstSegment snapshotConfig.σ snapshotConfig.tick snapshotConfig.steps
      0x800043ec#64 0#64 firstSegmentL [] snapshot_readyFacts.good
      snapshot_readyFacts.pc physicalRegs_minstret firstSegment_regs
      (by decide) firstSegment_facts (by decide) snapshot_readyFacts.tick
  refine ⟨⟨σ', i', snapshotConfig.steps + evalBlocksFuel firstSegment⟩, hs,
    { good := hG, tick := hi, steps := rfl, pc := hp, mem := ?_, regs := hr,
      sp := gholds_lookup _ hr rfl, a0 := gholds_lookup _ hr rfl,
      minstret := hmi, out := ho, payload := ?_, tohost := ?_ }⟩
  · change σ'.mem = writeLog snapshotMem firstSegmentLog
    change σ'.mem = writeLog snapshotMem firstSegmentEval.log at hm
    rwa [firstSegment_log] at hm
  · exact (hframe Register.htif_payload_writes (by decide) (by decide)).trans
      physicalRegs_htif_payload_writes
  · exact (hframe Register.htif_tohost (by decide) (by decide)).trans
      physicalRegs_htif_tohost

/-- Exact data at the first call seam, for the remaining trace certificates. -/
def firstTraceData : TraceData :=
  { pc := 0x80004424#64, regs := firstSegmentEval.regs,
    log := firstSegmentLog, out := #[], payload := 0#4 }

theorem FirstSegmentPost.traceHolds {c : Config} (h : FirstSegmentPost c) :
    TraceHolds firstTraceData c where
  good := h.good
  tick := h.tick
  pc := h.pc
  minstret := h.minstret
  regs := h.regs
  mem := h.mem
  out := h.out
  payload := h.payload

theorem snapshot_firstTrace :
    ∃ c, Steps snapshotConfig c ∧ TraceHolds firstTraceData c := by
  obtain ⟨c, hs, hp⟩ := snapshot_firstSegment
  exact ⟨c, hs, hp.traceHolds⟩

#print axioms snapshot_firstTrace

#print axioms firstSegment_facts
#print axioms snapshot_firstSegment

end Vsa.Sim.OutputAliasLoaded
