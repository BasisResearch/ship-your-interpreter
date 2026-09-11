import Vsa.Sim.DivSpec3
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.SegEffect

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.MemRepr

namespace Vsa.Sim

/-- Signed division entry, including the wrapping overflow input. -/
structure DivWrapPre (g : (R : Register) → Option (RegisterType R))
    (n d r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  division : Code.__divdi3Loaded c.σ.mem
  wrapper : Code.__umoddi3Loaded c.σ.mem
  core : Code.__hidden___udivdi3Loaded c.σ.mem
  mem : c.σ.mem = m0
  output : c.σ.sailOutput = out
  pc : c.σ.regs.get? .PC = some 0x800046a4#64
  numerator : c.σ.regs.get? .x10 = some n
  divisor : c.σ.regs.get? .x11 = some d
  ra : c.σ.regs.get? .x1 = some r
  minstret : ∃ w, c.σ.regs.get? .minstret = some w
  scratch12 : ∃ w, c.σ.regs.get? .x12 = some w
  scratch13 : ∃ w, c.σ.regs.get? .x13 = some w
  tick : c.tick < 2
  nonzero : d.toInt ≠ 0
  aligned : r.toNat % 4 = 0
  frame : ∀ R, NotWrittenD R → c.σ.regs.get? R = g R

/-- The signed quotient as a 64-bit word, with the actual memory and register frame. -/
structure DivWrapPost (g : (R : Register) → Option (RegisterType R))
    (n d r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  mem : c.σ.mem = m0
  output : c.σ.sailOutput = out
  pc : c.σ.regs.get? .PC = some r
  tick : c.tick < 2
  frame : ∀ R, NotWrittenD R → c.σ.regs.get? R = g R
  quotient : c.σ.regs.get? .x10 = some (BitVec.ofInt 64 (n.toInt.tdiv d.toInt))

/-- Convert the existing signed-result contract to its exact word result. -/
theorem DivWrapPost.of_signed
    {g : (R : Register) → Option (RegisterType R)} {n d r : BitVec 64}
    {m0 : Mem} {out : Array String} {c : Config}
    (h : divdi3_post g n d r m0 out c) : DivWrapPost g n d r m0 out c := by
  obtain ⟨good, mem, output, pc, tick, frame, result, value, quotient⟩ := h
  have word : BitVec.ofInt 64 (n.toInt.tdiv d.toInt) = result := by
    rw [← quotient, BitVec.ofInt_toInt]
  exact ⟨good, mem, output, pc, tick, frame, word.symm ▸ value⟩

/- The selected blocks emitted by gen_fn.py for __divdi3 and __umoddi3. -/
#derive_case divOverflowBranchSeg chain []
  terminator ⟨0x800046a4#64, 0x06054063#32, 0x63#8, 0x40#8, 0x05#8, 0x06#8,
    .br bop.BLT true, 10, 0, 0x0060#13, 0#21, 0#12⟩

#derive_case divOverflowDividendSeg chain
  [(0x80004704#64, 0x40a00533#32)]
    terminator ⟨0x80004708#64, 0x00b04863#32, 0x63#8, 0x48#8, 0xb0#8, 0x00#8,
      .br bop.BLT false, 0, 11, 0x0010#13, 0#21, 0#12⟩

#derive_case divOverflowDivisorSeg chain
  [(0x8000470c#64, 0x40b005b3#32)]
    terminator ⟨0x80004710#64, 0xf9dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xf9#8,
      .j, 0, 0, 0#13, 0x1fff9c#21, 0#12⟩

def divOverflowKeep (R : Register) : Bool := decide (NotWrittenD R)

theorem divOverflowWord :
    (0x8000000000000000#64 / 1#64 : BitVec 64) =
      BitVec.ofInt 64 ((0x8000000000000000#64 : BitVec 64).toInt.tdiv
        (0xffffffffffffffff#64 : BitVec 64).toInt) := by decide

theorem divOverflowNegMin :
    (0#64 - 0x8000000000000000#64 : BitVec 64) = 0x8000000000000000#64 := by decide

theorem divOverflowNegOne :
    (0#64 - 0xffffffffffffffff#64 : BitVec 64) = 1#64 := by decide

def divOverflowInput (r w12 w13 : BitVec 64) : GRegs :=
  [(10, 0x8000000000000000#64), (11, 0xffffffffffffffff#64),
    (1, r), (12, w12), (13, w13)]

def divOverflowMagnitudes (r w12 w13 : BitVec 64) : GRegs :=
  [(10, 0x8000000000000000#64), (11, 1#64), (1, r), (12, w12), (13, w13)]

theorem divOverflowBranch_run (c : Config) (r w12 w13 vm : BitVec 64)
    (good : GoodState c.σ) (pc : c.σ.regs.get? .PC = some 0x800046a4#64)
    (mi : c.σ.regs.get? .minstret = some vm) (tick : c.tick < 2)
    (loaded : Code.__divdi3Loaded c.σ.mem)
    (held : GHolds c.σ (divOverflowInput r w12 w13)) :
    ∃ after, SelectedFramedSegResult divOverflowBranchSeg (divOverflowInput r w12 w13) []
      0x800046a4#64 (fun _ => False) divOverflowKeep (divOverflowInput r w12 w13) c after := by
  have facts : ChainFacts c.σ.mem c.σ.mem (divOverflowInput r w12 w13) []
      divOverflowBranchSeg := by
    chain_facts loaded with "Vsa.Sim.Code.__divdi3_at_"
    change guardB bop.BLT 0x8000000000000000#64 0#64 = true
    decide
  exact segEval_selected_framed divOverflowBranchSeg (divOverflowInput r w12 w13) []
    0x800046a4#64 vm (fun _ => False) divOverflowKeep (divOverflowInput r w12 w13) c
    good pc mi held (by show KeysOK [10, 11, 1, 12, 13]; decide) facts
    (by show ChainOK 0x800046a4#64 [10, 11, 1, 12, 13] _; decide) tick
    (fun _ _ => rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩)

theorem divOverflowDividend_run (c : Config) (r w12 w13 vm : BitVec 64)
    (good : GoodState c.σ) (pc : c.σ.regs.get? .PC = some 0x80004704#64)
    (mi : c.σ.regs.get? .minstret = some vm) (tick : c.tick < 2)
    (loaded : Code.__umoddi3Loaded c.σ.mem)
    (held : GHolds c.σ (divOverflowInput r w12 w13)) :
    ∃ after, SelectedFramedSegResult divOverflowDividendSeg (divOverflowInput r w12 w13) []
      0x80004704#64 (fun _ => False) divOverflowKeep (divOverflowInput r w12 w13) c after := by
  have facts : ChainFacts c.σ.mem c.σ.mem (divOverflowInput r w12 w13) []
      divOverflowDividendSeg := by
    chain_facts loaded with "Vsa.Sim.Code.__umoddi3_at_"
    change guardB bop.BLT 0#64 0xffffffffffffffff#64 = false
    decide
  exact segEval_selected_framed divOverflowDividendSeg (divOverflowInput r w12 w13) []
    0x80004704#64 vm (fun _ => False) divOverflowKeep (divOverflowInput r w12 w13) c
    good pc mi held (by show KeysOK [10, 11, 1, 12, 13]; decide) facts
    (by show ChainOK 0x80004704#64 [10, 11, 1, 12, 13] _; decide) tick
    (fun _ _ => rfl) (by decide) (by decide)
    (by exact ⟨congrArg some divOverflowNegMin, rfl, rfl, rfl, rfl, trivial⟩)

theorem divOverflowDivisor_run (c : Config) (r w12 w13 vm : BitVec 64)
    (good : GoodState c.σ) (pc : c.σ.regs.get? .PC = some 0x8000470c#64)
    (mi : c.σ.regs.get? .minstret = some vm) (tick : c.tick < 2)
    (loaded : Code.__umoddi3Loaded c.σ.mem)
    (held : GHolds c.σ (divOverflowInput r w12 w13)) :
    ∃ after, SelectedFramedSegResult divOverflowDivisorSeg (divOverflowInput r w12 w13) []
      0x8000470c#64 (fun _ => False) divOverflowKeep (divOverflowMagnitudes r w12 w13) c after := by
  have facts : ChainFacts c.σ.mem c.σ.mem (divOverflowInput r w12 w13) []
      divOverflowDivisorSeg := by
    chain_facts loaded with "Vsa.Sim.Code.__umoddi3_at_"
  exact segEval_selected_framed divOverflowDivisorSeg (divOverflowInput r w12 w13) []
    0x8000470c#64 vm (fun _ => False) divOverflowKeep (divOverflowMagnitudes r w12 w13) c
    good pc mi held (by show KeysOK [10, 11, 1, 12, 13]; decide) facts
    (by show ChainOK 0x8000470c#64 [10, 11, 1, 12, 13] _; decide) tick
    (fun _ _ => rfl) (by decide) (by decide)
    (by exact ⟨rfl, congrArg some divOverflowNegOne, rfl, rfl, rfl, trivial⟩)

/-- The overflow path negates both operands and returns the unsigned quotient unchanged. -/
theorem divdi3_overflow_spec (g : (R : Register) → Option (RegisterType R))
    (r : BitVec 64) (m0 : Mem) (out : Array String) :
    Triple (DivWrapPre g 0x8000000000000000#64 0xffffffffffffffff#64 r m0 out)
      (DivWrapPost g 0x8000000000000000#64 0xffffffffffffffff#64 r m0 out) := by
  intro c pre
  obtain ⟨w12, h12⟩ := pre.scratch12
  obtain ⟨w13, h13⟩ := pre.scratch13
  obtain ⟨vm, hvm⟩ := pre.minstret
  have held : GHolds c.σ (divOverflowInput r w12 w13) :=
    ⟨pre.numerator, pre.divisor, pre.ra, h12, h13, trivial⟩
  obtain ⟨negative, head⟩ := divOverflowBranch_run c r w12 w13 vm
    pre.good pre.pc hvm pre.tick pre.division held
  have headMem : negative.σ.mem = c.σ.mem := head.mem
  obtain ⟨vmN, hvmN⟩ := head.minstret
  obtain ⟨dividend, hn⟩ := divOverflowDividend_run negative r w12 w13 vmN
    head.good head.pc hvmN head.tick (headMem.symm ▸ pre.wrapper) head.selected_regs
  have dividendMem : dividend.σ.mem = c.σ.mem := hn.mem.trans headMem
  obtain ⟨vmD, hvmD⟩ := hn.minstret
  obtain ⟨core, normalized⟩ := divOverflowDivisor_run dividend r w12 w13 vmD
    hn.good hn.pc hvmD hn.tick (dividendMem.symm ▸ pre.wrapper) hn.selected_regs
  have coreMem : core.σ.mem = c.σ.mem := normalized.mem.trans dividendMem
  obtain ⟨hnum, hden, hra, h12, h13, _⟩ := normalized.selected_regs
  obtain ⟨after, run, good, mem, output, pc, quotient, _remainder, _ra, tick, frame, _mi⟩ :=
    core_call_tail_f 0x8000000000000000#64 1#64 r r m0 out core normalized.good
      (coreMem.symm ▸ pre.core) (coreMem.trans pre.mem)
      (normalized.output.trans (hn.output.trans (head.output.trans pre.output))) normalized.pc
      hnum hden hra ⟨w12, h12⟩ ⟨w13, h13⟩ normalized.minstret normalized.tick
      (by decide) pre.aligned
  refine ⟨after, head.steps.trans (hn.steps.trans (normalized.steps.trans run)),
    good, mem, output, pc, tick, ?_, ?_⟩
  · intro R hR
    have kept : divOverflowKeep R = true := by
      simpa only [divOverflowKeep, decide_eq_true_eq] using hR
    exact (frame R hR.nw).trans ((normalized.reg_frame R kept).trans
      ((hn.reg_frame R kept).trans ((head.reg_frame R kept).trans (pre.frame R hR))))
  · rw [← divOverflowWord]
    exact quotient

/-- Signed division returns the wrapped quotient for every nonzero divisor. -/
theorem divdi3_wrap_spec (g : (R : Register) → Option (RegisterType R))
    (n d r : BitVec 64) (m0 : Mem) (out : Array String) :
    Triple (DivWrapPre g n d r m0 out) (DivWrapPost g n d r m0 out) := by
  intro c pre
  by_cases overflow : n.toInt = -2^63 ∧ d.toInt = -1
  · have hn : n = 0x8000000000000000#64 := by
      apply BitVec.eq_of_toInt_eq
      exact overflow.1
    have hd : d = 0xffffffffffffffff#64 := by
      apply BitVec.eq_of_toInt_eq
      exact overflow.2
    subst n d
    exact divdi3_overflow_spec g r m0 out c pre
  · obtain ⟨after, run, result⟩ := divdi3_spec g n d r m0 out c
      ⟨pre.good, pre.division, pre.wrapper, pre.core, pre.mem, pre.output,
        pre.pc, pre.numerator, pre.divisor, pre.ra, pre.minstret, pre.scratch12,
        pre.scratch13, pre.tick, pre.nonzero, overflow, pre.aligned, pre.frame⟩
    exact ⟨after, run, DivWrapPost.of_signed result⟩

#print axioms DivWrapPost.of_signed
#print axioms divOverflowWord
#print axioms divOverflowNegMin
#print axioms divOverflowNegOne
#print axioms divOverflowBranch_run
#print axioms divOverflowDividend_run
#print axioms divOverflowDivisor_run
#print axioms divdi3_overflow_spec
#print axioms divdi3_wrap_spec

end Vsa.Sim
