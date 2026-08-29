import Vsa.Sim.DivDispatchSeg
import Vsa.Sim.DivTailSites
import Vsa.Sim.BinOpValueTails

/-!
# `EvalDivValueTail` — the three concrete machine bridges for the `.div` value tail

`divValueTail` (`BinOpValueTails.lean`) composes the two real call seams
(`__divdi3` via `divdi3_spec`, `value_int` via `value_int_spec`) and reduces the
`.div` arm's item-2 + item-3 to three concrete machine bridges `pre`/`stage`/`suf`
(see `experiments/binop-value-tail-wiring.md`).  This file builds those bridges on
the generated `DivTailSites` battery (`0x8000381c → 0x80003830`), each a short
straight-line/`jal` step run mirroring the corresponding leg of the landed
`blockC_mul` (`rows/EvalMulRow.lean`).

* **`divPreBridge`** — `DivDispatchPost` (`0x8000381c`, `x10=Wl`, `x11=Wr`) plus the
  `jal __divdi3` link → `divdi3_pre Wl Wr 0x80003820 mA`.  The single jal at
  `0x8000381c`; the `__divdi3`-entry side conditions (loaded predicates on the
  post-dispatch memory `mA`, the divisor-nonzero + no-`INT64_MIN,-1`-overflow value
  facts, the `x12`/`x13` scratch presence) are surfaced as hypotheses, discharged by
  the eval-case caller exactly as `blockC_mul`'s big precondition bundle supplies the
  `__muldi3` analogues.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 4000000

namespace Vsa.Sim

/-- **The `.div` `pre` bridge.**  From `DivDispatchPost` (parked at `0x8000381c`
with the `__divdi3` arguments `x10=Wl`, `x11=Wr` staged and `mem = mA`), the single
`jal __divdi3 @0x8000381c` links `x1 := 0x80003820` and lands the callee entry
`0x800046a4`, delivering `divdi3_pre Wl Wr 0x80003820 mA`.  The extra `__divdi3`
entry obligations — the three `divdi3`/`udivdi3` code-image loaded predicates on the
post-dispatch memory `mA`, the divisor-nonzero (`Wr.toInt ≠ 0`) and
no-`INT64_MIN,-1`-overflow (`¬(Wl.toInt = -2^63 ∧ Wr.toInt = -1)`) value facts, and
the `x12`/`x13` scratch presence — are caller obligations, mirroring the way
`blockC_mul` feeds `muldi3_pre` from its precondition bundle. -/
theorem divPreBridge (gd gpre : (R : Register) → Option (RegisterType R))
    (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 mA : Std.ExtHashMap Nat (BitVec 8)) (outD : Array String)
    (hmA : mA = writeLog m0
      (evalBlocks divDispatch (SegEvalState.init (divDispL v2 sret Wr Wl) lds)).log)
    (hee : Vsa.Sim.Code.Eval_exprLoaded mA)
    (hdl : Vsa.Sim.Code.__divdi3Loaded mA)
    (hul : Vsa.Sim.Code.__umoddi3Loaded mA)
    (hcl : __hidden___udivdi3Loaded mA)
    (hWr : Wr.toInt ≠ 0)
    (hov : ¬(Wl.toInt = -2^63 ∧ Wr.toInt = -1)) :
    Triple
      (fun c => DivDispatchPost v2 sret Wr Wl lds m0 outD gpre c ∧
        (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = gd R))
      (divdi3_pre gd Wl Wr (0x80003820#64) mA outD) := by
  intro c hpre
  obtain ⟨hDDP, hgd⟩ := hpre
  obtain ⟨hG, hmem, hpc, hx10, hx11, hx9, hx2, ⟨w12, hx12⟩, ⟨w13, hx13⟩, htick, hout, _hframeD⟩ := hDDP
  have hmemA : c.σ.mem = mA := by rw [hmem]; exact hmA.symm
  obtain ⟨vmi, hmi⟩ := hG.minstret
  -- the jal at 0x8000381c
  obtain ⟨σ', i', hstep, hi', hG', hmemeq', hobs⟩ :=
    site_8000381c_ee c.σ c.tick c.steps (0x8000381c#64) vmi hG hpc hmi
      (by rw [hmemA]; exact hee) rfl htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  -- register / pc facts from the jal ReadsLikePost
  have hpc' : σ'.regs.get? Register.PC = some (0x800046a4#64) := by
    have := obs_jal_pc hobs
    rwa [show ((0x8000381c#64 : BitVec 64) + sign_extend (m := 64) (0x000e88#21))
      = 0x800046a4#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink' : σ'.regs.get? Register.x1 = some (0x80003820#64) := by
    have := obs_jal_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000381c#64 : BitVec 64) 4 = (0x80003820#64 : BitVec 64)
      from by decide] at this
  have hx10' : σ'.regs.get? Register.x10 = some Wl :=
    obs_jal_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx10
  have hx11' : σ'.regs.get? Register.x11 = some Wr :=
    obs_jal_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx11
  have hx12' : σ'.regs.get? Register.x12 = some w12 :=
    obs_jal_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx12
  have hx13' : σ'.regs.get? Register.x13 = some w13 :=
    obs_jal_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx13
  have hmemA' : σ'.mem = mA := by rw [hmemeq']; exact hmemA
  have hout' : σ'.sailOutput = outD := by
    rw [hobs.out, sailOutput_sigmaPost_jal]; exact hout
  have hframe' : ∀ R : Register, NotWrittenD R → σ'.regs.get? R = gd R := by
    intro R hR
    rw [frame_jal hobs R hR.2.1 hR.nw]; exact hgd R hR
  refine ⟨⟨σ', i', c.steps + 1⟩, Steps.single hstep', ?_⟩
  refine ⟨hG', ?_, ?_, ?_, hmemA', hout', hpc', hx10', hx11', hlink', obs_jal_minstret hobs,
    ⟨w12, hx12'⟩, ⟨w13, hx13'⟩, hi', hWr, hov, by decide, hframe'⟩
  · rw [hmemA']; exact hdl
  · rw [hmemA']; exact hul
  · rw [hmemA']; exact hcl

#print axioms divPreBridge

end Vsa.Sim
