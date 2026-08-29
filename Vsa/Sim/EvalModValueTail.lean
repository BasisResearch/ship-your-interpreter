import Vsa.Sim.ModDispatchStrong
import Vsa.Sim.ModTailSites
import Vsa.Sim.BinOpValueTails

/-!
# `EvalModValueTail` — the `.mod` `pre` machine bridge

The `.mod` analogue of `EvalDivValueTail.lean` (`divPreBridge`).  `modValueTail`
(`BinOpValueTails.lean`) composes the two real call seams (`__moddi3` via the
strong `moddi3_spec`, `value_int` via `value_int_spec`); this file builds the
`pre` bridge on the generated `ModTailSites` battery.

* **`modPreBridge`** — `ModDispatchPostS` (`0x800037c4`, `x10=Wl`, `x11=Wr`) plus
  the `jal __moddi3` link → `moddi3_pre gd Wl Wr 0x800037c8 mA outD`.  The single
  jal at `0x800037c4`; `__moddi3`'s entry side conditions (loaded predicates on the
  post-dispatch memory `mA`, the divisor-nonzero value fact `Wr.toInt ≠ 0` — mod has
  NO `INT64_MIN` overflow exclusion, `Int.tmod` never overflows — and the `x12`/`x13`
  scratch presence) are surfaced as hypotheses, discharged by the eval-case caller
  exactly as `blockC_div`.

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

/-- `__moddi3Loaded` survives on any memory agreeing over `[0x80004728, 0x80004764)`. -/
theorem loaded_moddi3_agreeP (m m' : Mem)
    (ha : ∀ a, (0x80004728 ≤ a ∧ a < 0x80004764) → m[a]? = m'[a]?)
    (h : Vsa.Sim.Code.__moddi3Loaded m) : Vsa.Sim.Code.__moddi3Loaded m' := by
  simp only [Vsa.Sim.Code.__moddi3Loaded, Vsa.Sim.Code.__moddi3Chunk0] at h ⊢
  repeat' apply And.intro
  all_goals (first
    | (rw [← ha _ (by omega)]; simp_all only [])
    | simp_all only [])

/-- **The `.mod` `pre` bridge.**  From `ModDispatchPostS` (parked at `0x800037c4`
with the `__moddi3` arguments `x10=Wl`, `x11=Wr` staged and `mem = mA`), the single
`jal __moddi3 @0x800037c4` links `x1 := 0x800037c8` and lands the callee entry
`0x80004728`, delivering `moddi3_pre gd Wl Wr 0x800037c8 mA outD`.  The extra
`__moddi3` entry obligations — the `__moddi3`/`__hidden___udivdi3` code-image loaded
predicates on the post-dispatch memory `mA`, the divisor-nonzero value fact
(`Wr.toInt ≠ 0`), and the `x12`/`x13` scratch presence — are caller obligations. -/
theorem modPreBridge (gd gpre : (R : Register) → Option (RegisterType R))
    (v2 sret Wr Wl : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 mA : Std.ExtHashMap Nat (BitVec 8)) (outD : Array String)
    (hmA : mA = writeLog m0
      (evalBlocks modDispatch (SegEvalState.init (modDispLS v2 sret Wr Wl) lds)).log)
    (hee : Vsa.Sim.Code.Eval_exprLoaded mA)
    (hml : Vsa.Sim.Code.__moddi3Loaded mA)
    (hcl : __hidden___udivdi3Loaded mA)
    (hWr : Wr.toInt ≠ 0) :
    Triple
      (fun c => ModDispatchPostS v2 sret Wr Wl lds m0 outD gpre c ∧
        (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = gd R))
      (moddi3_pre gd Wl Wr (0x800037c8#64) mA outD) := by
  intro c hpre
  obtain ⟨hMDP, hgd⟩ := hpre
  obtain ⟨hG, hmem, hpc, hx10, hx11, hx9, hx2, ⟨w12, hx12⟩, ⟨w13, hx13⟩, htick, hout, _hframeD⟩ := hMDP
  have hmemA : c.σ.mem = mA := by rw [hmem]; exact hmA.symm
  obtain ⟨vmi, hmi⟩ := hG.minstret
  -- the jal at 0x800037c4
  obtain ⟨σ', i', hstep, hi', hG', hmemeq', hobs⟩ :=
    site_800037c4_ee c.σ c.tick c.steps (0x800037c4#64) vmi hG hpc hmi
      (by rw [hmemA]; exact hee) rfl htick
  have hstep' : Step c ⟨σ', i', c.steps + 1⟩ := by cases c; exact hstep
  have hpc' : σ'.regs.get? Register.PC = some (0x80004728#64) := by
    have := obs_jal_pc hobs
    rwa [show ((0x800037c4#64 : BitVec 64) + sign_extend (m := 64) (0x000f64#21))
      = 0x80004728#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink' : σ'.regs.get? Register.x1 = some (0x800037c8#64) := by
    have := obs_jal_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800037c4#64 : BitVec 64) 4 = (0x800037c8#64 : BitVec 64)
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
  refine ⟨hG', ?_, ?_, hmemA', hout', hpc', hx10', hx11', hlink', obs_jal_minstret hobs,
    ⟨w12, hx12'⟩, ⟨w13, hx13'⟩, hi', hWr, by decide, hframe'⟩
  · rw [hmemA']; exact hml
  · rw [hmemA']; exact hcl

#print axioms modPreBridge

end Vsa.Sim
