import Vsa.Sim.DivWrap
import Vsa.Sim.DivSpec3T

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine (Config RunT)
open Vsa.Logic Vsa.MemRepr

namespace Vsa.Sim

theorem divdi3_overflow_specT (r : BitVec 64) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 out,
      TripleT τ (DivWrapPre g 0x8000000000000000#64 0xffffffffffffffff#64 r m0 out)
        (DivWrapPost g 0x8000000000000000#64 0xffffffffffffffff#64 r m0 out) := by
  obtain ⟨τf, hT⟩ := core_call_tail_fT 0x8000000000000000#64 1#64 r (by decide) halign
  refine ⟨pcsC divOverflowBranchSeg ++ pcsC divOverflowDividendSeg ++ pcsC divOverflowDivisorSeg ++ τf,
    fun g m0 out c pre => ?_⟩
  obtain ⟨w12, h12⟩ := pre.scratch12
  obtain ⟨w13, h13⟩ := pre.scratch13
  obtain ⟨vm, hvm⟩ := pre.minstret
  have held : GHolds c.σ (divOverflowInput r w12 w13) :=
    ⟨pre.numerator, pre.divisor, pre.ra, h12, h13, trivial⟩
  have facts1 : ChainFacts c.σ.mem c.σ.mem (divOverflowInput r w12 w13) []
      divOverflowBranchSeg := by
    chain_facts pre.division
    change guardB bop.BLT 0x8000000000000000#64 0#64 = true
    decide
  obtain ⟨negative, head, hrun1⟩ := segEval_selected_framedT divOverflowBranchSeg
    (divOverflowInput r w12 w13) [] 0x800046a4#64 vm (fun _ => False) divOverflowKeep
    (divOverflowInput r w12 w13) c pre.good pre.pc hvm held
    (by show KeysOK [10, 11, 1, 12, 13]; decide) facts1
    (by show ChainOK 0x800046a4#64 [10, 11, 1, 12, 13] _; decide) pre.tick
    (fun _ _ => rfl) (by decide) (by decide) (by exact ⟨rfl, rfl, rfl, rfl, rfl, trivial⟩)
  have headMem : negative.σ.mem = c.σ.mem := head.mem_eq
  obtain ⟨vmN, hvmN⟩ := head.minstret
  have facts2 : ChainFacts negative.σ.mem negative.σ.mem (divOverflowInput r w12 w13) []
      divOverflowDividendSeg := by
    chain_facts (headMem.symm ▸ pre.wrapper : Code.__umoddi3Loaded negative.σ.mem)
    change guardB bop.BLT 0#64 0xffffffffffffffff#64 = false
    decide
  obtain ⟨dividend, hn, hrun2⟩ := segEval_selected_framedT divOverflowDividendSeg
    (divOverflowInput r w12 w13) [] 0x80004704#64 vmN (fun _ => False) divOverflowKeep
    (divOverflowInput r w12 w13) negative head.good head.pc hvmN head.selected_regs
    (by show KeysOK [10, 11, 1, 12, 13]; decide) facts2
    (by show ChainOK 0x80004704#64 [10, 11, 1, 12, 13] _; decide) head.tick
    (fun _ _ => rfl) (by decide) (by decide)
    (by exact ⟨congrArg some divOverflowNegMin, rfl, rfl, rfl, rfl, trivial⟩)
  have dividendMem : dividend.σ.mem = c.σ.mem := hn.mem_eq.trans headMem
  obtain ⟨vmD, hvmD⟩ := hn.minstret
  have facts3 : ChainFacts dividend.σ.mem dividend.σ.mem (divOverflowInput r w12 w13) []
      divOverflowDivisorSeg := by
    chain_facts (dividendMem.symm ▸ pre.wrapper : Code.__umoddi3Loaded dividend.σ.mem)
  obtain ⟨core, normalized, hrun3⟩ := segEval_selected_framedT divOverflowDivisorSeg
    (divOverflowInput r w12 w13) [] 0x8000470c#64 vmD (fun _ => False) divOverflowKeep
    (divOverflowMagnitudes r w12 w13) dividend hn.good hn.pc hvmD hn.selected_regs
    (by show KeysOK [10, 11, 1, 12, 13]; decide) facts3
    (by show ChainOK 0x8000470c#64 [10, 11, 1, 12, 13] _; decide) hn.tick
    (fun _ _ => rfl) (by decide) (by decide)
    (by exact ⟨rfl, congrArg some divOverflowNegOne, rfl, rfl, rfl, trivial⟩)
  have coreMem : core.σ.mem = c.σ.mem := normalized.mem_eq.trans dividendMem
  obtain ⟨hnum, hden, hra, h12', h13', _⟩ := normalized.selected_regs
  obtain ⟨after, run, good, mem, output, pc, quotient, _remainder, _ra, tick, frame, _mi⟩ :=
    hT m0 out core normalized.good (coreMem.symm ▸ pre.core) (coreMem.trans pre.mem)
      (normalized.output.trans (hn.output.trans (head.output.trans pre.output))) normalized.pc
      hnum hden hra ⟨w12, h12'⟩ ⟨w13, h13'⟩ normalized.minstret normalized.tick
  refine ⟨after, ((hrun1.trans hrun2).trans hrun3).trans run, good, mem, output, pc, tick, ?_, ?_⟩
  · intro R hR
    have kept : divOverflowKeep R = true := by
      simpa only [divOverflowKeep, decide_eq_true_eq] using hR
    exact (frame R hR.nw).trans ((normalized.reg_frame R kept).trans
      ((hn.reg_frame R kept).trans ((head.reg_frame R kept).trans (pre.frame R hR))))
  · rw [← divOverflowWord]
    exact quotient

theorem divdi3_wrap_specT (n d r : BitVec 64) (hd0 : d.toInt ≠ 0) (halign : r.toNat % 4 = 0) :
    ∃ τ : List (BitVec 64), ∀ g m0 out,
      TripleT τ (DivWrapPre g n d r m0 out) (DivWrapPost g n d r m0 out) := by
  by_cases overflow : n.toInt = -2^63 ∧ d.toInt = -1
  · have hn : n = 0x8000000000000000#64 := by
      apply BitVec.eq_of_toInt_eq
      exact overflow.1
    have hd : d = 0xffffffffffffffff#64 := by
      apply BitVec.eq_of_toInt_eq
      exact overflow.2
    subst n d
    exact divdi3_overflow_specT r halign
  · obtain ⟨τ, hT⟩ := divdi3_specT n d r hd0 overflow halign
    refine ⟨τ, fun g m0 out c pre => ?_⟩
    obtain ⟨after, run, result⟩ := hT g m0 out c
      ⟨pre.good, pre.division, pre.wrapper, pre.core, pre.mem, pre.output,
        pre.pc, pre.numerator, pre.divisor, pre.ra, pre.minstret, pre.scratch12,
        pre.scratch13, pre.tick, pre.nonzero, overflow, pre.aligned, pre.frame⟩
    exact ⟨after, run, DivWrapPost.of_signed result⟩

end Vsa.Sim
