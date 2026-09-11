import Vsa.Sim.DivWrap
import Vsa.Sim.EvalDivValueTail
import Vsa.Sim.BridgeSegFull

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.Logic Vsa.MemRepr

namespace Vsa.Sim

/-- The division call preserves every register in the wrapper's existing frame. -/
theorem NotWrittenD.jal_avoids {R : Register} (h : NotWrittenD R) :
    ∀ rr ∈ Register.x1 :: noiseRegs, (rr == R) = false := by
  rcases h with ⟨⟨_, _, _, _, pc, next, mi, inc, cycle, time, ip⟩, ra, _⟩
  simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false]
  intro rr member
  rcases member with h | h | h | h | h | h | h | h <;> subst rr <;> assumption

/-- The actual interpreter JAL supplies the wrapping division contract. -/
theorem divWrapPreBridge (gd gpre : (R : Register) → Option (RegisterType R))
    (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 mA : Mem) (out : Array String)
    (hmA : mA = writeLog m0
      (evalBlocks divDispatch (SegEvalState.init (divDispL v2 sret Wr Wl) lds)).log)
    (hee : Code.Eval_exprLoaded mA) (hdl : Code.__divdi3Loaded mA)
    (hul : Code.__umoddi3Loaded mA) (hcl : Code.__hidden___udivdi3Loaded mA)
    (nonzero : Wr.toInt ≠ 0) :
    Triple
      (fun c => DivDispatchPost v2 sret Wr Wl lds m0 out gpre c ∧
        (∀ R, NotWrittenD R → c.σ.regs.get? R = gd R))
      (DivWrapPre gd Wl Wr 0x80003820#64 mA out) := by
  intro c input
  obtain ⟨dispatch, frame⟩ := input
  obtain ⟨good, mem, pc, hn, hd, _dst, _sp, h12, h13, tick, output, _frame⟩ := dispatch
  have memory : c.σ.mem = mA := mem.trans hmA.symm
  obtain ⟨vm, hvm⟩ := good.minstret
  obtain ⟨σ, i, step, hi, hg, hm, ho⟩ := site_8000381c_ee c.σ c.tick c.steps
    0x8000381c#64 vm good pc hvm (memory.symm ▸ hee) rfl tick
  have J := jalCallFacts_of_obs step hi hg hm ho
    (by decide : (0x8000381c#64 : BitVec 64) + sign_extend (m := 64) 0x000e88#21 = 0x800046a4#64)
  have memory' : σ.mem = mA := J.mem.trans memory
  refine ⟨⟨σ, i, c.steps + 1⟩, Steps.single J.step,
    { good := J.good, division := memory'.symm ▸ hdl, wrapper := memory'.symm ▸ hul
      core := memory'.symm ▸ hcl, mem := memory'
      output := J.frame.out.trans output, pc := J.pc
      numerator := J.nonra 10 (by decide) (by decide) (by decide) Wl hn
      divisor := J.nonra 11 (by decide) (by decide) (by decide) Wr hd
      ra := J.ra, minstret := J.minstret
      scratch12 := ?_, scratch13 := ?_, tick := J.tick
      nonzero := nonzero, aligned := by decide
      frame := fun R hR => (J.frame.frame R hR.jal_avoids).trans (frame R hR) }⟩
  · obtain ⟨w, hw⟩ := h12
    exact ⟨w, J.nonra 12 (by decide) (by decide) (by decide) w hw⟩
  · obtain ⟨w, hw⟩ := h13
    exact ⟨w, J.nonra 13 (by decide) (by decide) (by decide) w hw⟩

#print axioms NotWrittenD.jal_avoids
#print axioms divWrapPreBridge

end Vsa.Sim
