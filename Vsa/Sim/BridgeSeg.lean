import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.FrameMeta
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.EnvNewSpec

/-!
# `BridgeSeg` — the Shape-A `env_define` bridge, factored over the seg machinery

Every `env_define` Shape-A bridge (`bridgeStrlenPre`/`bridgeMallocPre`/
`bridgeCapCompute`/`bridgeNamesToVals`) is the SAME shape:

```
  <straight-line argument-marshalling body>   -- a #derive_case seg (EnvDefSeg pattern)
  jal <callee>                                -- the Shape-D call seam
  ⟹  Triple (entry)  (calleePre ∧ carried-frame)
```

Before this file, each bridge hand-wrote a `*Prefix_run` lemma
(`capComputePrefix_run` is ~175 lines: 5 per-site `stepObs_*` lemmas ×~30 lines
each + the run threading + a hand per-register frame across all steps) and then a
`*_closed` repackager.

`BridgeSeg` factors the **whole run + jal seam + frame threading** into ONE
theorem `bridgeOfSeg`.  It composes:

* the `#derive_case` seg body run (via `segEval_sound`) — the whole `Steps` chain,
  computed end PC (`= jalPC`, the seg is the body *up to* the jal), computed
  marshalled registers `GHolds σ' out.regs`, and computed memory
  `writeLog m0 out.log`, all FREE (the seg's one kernel `decide` `hwf`);
* the `jal` step, supplied as ONE hypothesis `JalStep` — the bridge's existing
  per-callee `site_*_ed` jal lemma repackaged: each callee's jal word/offset/link
  differs, so it stays per-bridge, but its shape is uniform (a ~15-line
  `stepObs_jal` + `obs_jal_*` readbacks over the *parked* config);
* the register frame across the body, collapsed to the ABI callee-saved shape via
  `FrameMeta.abiFrame_of_wrChain` (ONE `decide`: `WrChainAvoidAbi bs`) — no
  per-site `get?_sigmaPost_*` threading;
* the footprint frame across the body, via `FrameMeta.memFrame_of_chain`.

## What's generic vs per-bridge

GENERIC (this file, `bridgeOfSeg`, ONE application per bridge):
  the seg run, the ABI frame collapse, the footprint frame, the `Steps` splice,
  the marshalled-register survival across the jal, and the minstret witness.

PER-BRIDGE (supplied to `bridgeOfSeg`):
  (i)   the seg def (`#derive_case`, 3 lines) + the entry pin list `L`;
  (ii)  `hwf : ChainOK` (the row's one `decide`) and `hAvoid : WrChainAvoidAbi bs`
        (one more `decide`);
  (iii) the `JalStep` datum — the ONE genuinely callee-specific seam (different
        jal word/offset/link per callee), a thin repackaging of the existing
        `site_*_ed` jal lemma over the parked config;
  (iv)  a thin `*_closed` wrapper turning the generic `BridgeLanded` post into the
        callee's own entry predicate (`ReallocPre`/`strlen_pre`/…) + carried
        frame, tying the computed marshalled args to the caller's `ofNat` ghosts —
        the `bridgeCapCompute_closed` body's last third, unchanged.

So a NEW bridge = seg def (3) + `JalStep` from the existing jal site lemma (~15) +
`bridgeOfSeg` application (~5) + `*_closed` wrapper (~40, all callee-pre
marshalling).  The ~175-line hand `*Prefix_run` collapses to the `JalStep` +
`bridgeOfSeg` application.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc (AbiPreserved)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-- **The per-callee `jal` seam, as a uniform datum.**  Given the config `σp`
parked at the *computed* jal PC (`= evalBlocksPC pc0 (init L lds) bs`, the seg
body's end) with the seg post established (`GoodState`, that PC, a `minstret`
witness), the bridge's own `jal` site lemma steps once to the callee entry:
* lands at `calleeEntry` (`PC`), links `x1 := link`;
* touches no memory (`σ2.mem = σp.mem`);
* preserves every register except `x1` (`nonRa`), so the marshalled args survive.

This is the ONLY genuinely callee-specific piece (the jal word/offset/link differ
per callee); a bridge proves it in ~15 lines from its existing `site_*_ed` jal
lemma over the parked config, exactly the last two steps of a hand `*Prefix_run`. -/
def JalStep (calleeEntry link : BitVec 64) (σp : MState) (ip up : Nat) : Prop :=
  ∃ (σ2 : MState) (i2 : Nat),
    Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
    σ2.mem = σp.mem ∧
    σ2.regs.get? Register.PC = some calleeEntry ∧
    σ2.regs.get? Register.x1 = some link ∧
    (∃ w, σ2.regs.get? Register.minstret = some w) ∧
    -- every GPR except the link `x1` survives (`gprGet`-level, the marshalled args):
    (∀ (n : Nat), 1 ≤ n → n ≤ 31 → n ≠ 1 →
      ∀ (w : BitVec 64), gprGet σp n = some w → gprGet σ2 n = some w) ∧
    -- ABI callee-saved frame of the jal step (jal writes only x1, x1 not callee-saved):
    (∀ R, AbiPreserved R = true → σ2.regs.get? R = σp.regs.get? R)

/-- **The pin list avoids `x1`** — no marshalled register is the link register.
First-order over `keysG L` (a concrete `List Nat` for a concrete seg outcome); a
bridge closes it with ONE `decide`.  This is what lets the marshalled args survive
the `jal` (which writes only `x1`). -/
def KeysAvoidRa (L : GRegs) : Prop := ∀ n ∈ keysG L, n ≠ 1

instance (L : GRegs) : Decidable (KeysAvoidRa L) := by unfold KeysAvoidRa; infer_instance

/-- Lift `GHolds` through the `jal` step: every pinned register is in `1..31`
(`KeysOK`) and differs from `x1` (`KeysAvoidRa`), so the `JalStep`'s `nonRa`
`gprGet`-transport carries each pin. -/
theorem gholds_of_jal {σp σ2 : MState}
    (hnonRa : ∀ (n : Nat), 1 ≤ n → n ≤ 31 → n ≠ 1 →
      ∀ (w : BitVec 64), gprGet σp n = some w → gprGet σ2 n = some w) :
    ∀ (L : GRegs), KeysOK (keysG L) → KeysAvoidRa L → GHolds σp L → GHolds σ2 L := by
  intro L
  induction L with
  | nil => intro _ _ _; exact trivial
  | cons p L ih =>
    obtain ⟨n, w⟩ := p
    intro hK hRa hL
    have hn := hK n (List.mem_cons_self ..)
    have hne : n ≠ 1 := hRa n (List.mem_cons_self ..)
    exact ⟨hnonRa n hn.1 hn.2 hne w hL.1,
      ih (fun k hk => hK k (List.mem_cons_of_mem _ hk))
        (fun k hk => hRa k (List.mem_cons_of_mem _ hk)) hL.2⟩

/-- **Build a `JalStep` from the raw `jal` observation** — the reusable jal-seam
glue, done ONCE.  Given the single `jal` `Step` and its `ReadsLikePost
(sigmaPost_jal σp jalPC vm imm x1 link)` observation (the exact output of any
`stepObs_jal` site lemma), plus the arithmetic tie `jalPC + sext imm =
calleeEntry`, this discharges every `JalStep` field: PC (`obs_jal_pc_env`), link
(`obs_jal_rd_env`), the `gprGet` nonRa transport (33-branch `obs_jal_other_env`),
and the ABI frame (`get?_sigmaPost_jal`).  A per-bridge jal glue is then the
`stepObs_jal` invocation + this one call. -/
theorem jalStep_of_obs {σp σ2 : MState} {ip up i2 : Nat}
    {jalPC vm : BitVec 64} {imm : BitVec 21} {calleeEntry link : BitVec 64}
    (hstep : Step ⟨σp, ip, up⟩ ⟨σ2, i2, up + 1⟩) (hi2 : i2 < 2) (hG2 : GoodState σ2)
    (hmem : σ2.mem = σp.mem)
    (hobs : ReadsLikePost σ2 (sigmaPost_jal σp jalPC vm imm Register.x1 link))
    (hce : jalPC + sign_extend (m := 64) imm = calleeEntry) :
    JalStep calleeEntry link σp ip up := by
  refine ⟨σ2, i2, hstep, hi2, hG2, hmem, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hce]; exact obs_jal_pc_env hobs
  · exact obs_jal_rd_env hobs (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact obs_jal_minstret_env hobs
  · -- nonRa: every GPR n ∈ 1..31, n ≠ 1 survives (33-branch dispatch on n).
    intro n hn1 hn31 hne w hw
    match n, hn1, hn31, hne, hw with
    | 0, h, _, _, _ => exact absurd h (by omega)
    | 1, _, _, hne, _ => exact absurd rfl hne
    | 2, _, _, _, hw => exact obs_jal_other_env hobs Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 3, _, _, _, hw => exact obs_jal_other_env hobs Register.x3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 4, _, _, _, hw => exact obs_jal_other_env hobs Register.x4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 5, _, _, _, hw => exact obs_jal_other_env hobs Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 6, _, _, _, hw => exact obs_jal_other_env hobs Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 7, _, _, _, hw => exact obs_jal_other_env hobs Register.x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 8, _, _, _, hw => exact obs_jal_other_env hobs Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 9, _, _, _, hw => exact obs_jal_other_env hobs Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 10, _, _, _, hw => exact obs_jal_other_env hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 11, _, _, _, hw => exact obs_jal_other_env hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 12, _, _, _, hw => exact obs_jal_other_env hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 13, _, _, _, hw => exact obs_jal_other_env hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 14, _, _, _, hw => exact obs_jal_other_env hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 15, _, _, _, hw => exact obs_jal_other_env hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 16, _, _, _, hw => exact obs_jal_other_env hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 17, _, _, _, hw => exact obs_jal_other_env hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 18, _, _, _, hw => exact obs_jal_other_env hobs Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 19, _, _, _, hw => exact obs_jal_other_env hobs Register.x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 20, _, _, _, hw => exact obs_jal_other_env hobs Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 21, _, _, _, hw => exact obs_jal_other_env hobs Register.x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 22, _, _, _, hw => exact obs_jal_other_env hobs Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 23, _, _, _, hw => exact obs_jal_other_env hobs Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 24, _, _, _, hw => exact obs_jal_other_env hobs Register.x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 25, _, _, _, hw => exact obs_jal_other_env hobs Register.x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 26, _, _, _, hw => exact obs_jal_other_env hobs Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 27, _, _, _, hw => exact obs_jal_other_env hobs Register.x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 28, _, _, _, hw => exact obs_jal_other_env hobs Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 29, _, _, _, hw => exact obs_jal_other_env hobs Register.x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 30, _, _, _, hw => exact obs_jal_other_env hobs Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | 31, _, _, _, hw => exact obs_jal_other_env hobs Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hw
    | k+32, _, h, _, _ => exact absurd h (by omega)
  · -- ABI frame: any callee-saved R differs from x1 + control, so passes through jal.
    intro R hR
    exact (hobs.1 R (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide))).trans
      (get?_sigmaPost_jal σp jalPC vm imm Register.x1 link R
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)) (abiPreserved_ne hR (by decide))
        (abiPreserved_ne hR (by decide)))

/-- **`bridgeOfSeg` — the factored Shape-A bridge combinator (∃-form).**

A drop-in replacement for a hand `*Prefix_run` (e.g. `capComputePrefix_run`).
From the entry state `σ` parked at the bridge entry `pc0` (`GHolds σ L`, the entry
memory `= m0`), it runs the `#derive_case` seg body `bs` (up to the jal) via
`segEval_sound`, then takes the `jal` step supplied by `hjal : JalStep …`, and
returns the whole landed run: parked at `calleeEntry`, `x1 = link`, the computed
marshalled registers `GHolds σ' out.regs` surviving the jal, memory
`writeLog m0 out.log`, a `minstret` witness, and the ABI callee-saved frame back
to the entry `σ` — everything the callee's `*_closed` wrapper needs.

* `hwf` — the seg's ONE kernel `decide` (`ChainOK pc0 (keysG L) bs`).
* `hAvoid` — the ABI-frame datum, ONE `decide` (`WrChainAvoidAbi bs`: no register
  the body writes is callee-saved).
* `hKeysOut`/`hRaOut` — two `decide`s on the concrete seg outcome keys (in `1..31`,
  none is `x1`), so the marshalled args survive the jal.
* `hjal` — the per-callee `JalStep` (the bridge's existing `site_*_ed` jal lemma).

The ~30-line per-register `get?_sigmaPost_*` frame chain each hand `*Prefix_run`
wrote is entirely replaced by `abiFrame_of_wrChain hAvoid` (one `decide`) for the
whole body; the jal's own (small) frame comes packaged in `JalStep`.  The concrete
`writeLog m0 out.log` memory is exposed directly — the per-store disjointness a
`*_closed` wrapper needs (e.g. the cap word) is read off it with
`getElem_writeMap4_disjoint`, exactly as the hand version does. -/
theorem bridgeOfSeg (bs : List BBlock) (L : GRegs) (lds : List (List (BitVec 8)))
    (σ : MState) (i u : Nat) (pc0 calleeEntry link vm : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some pc0)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hmem : σ.mem = m0)
    (hL : GHolds σ L)
    (hkeys : KeysOK (keysG L))
    (hfacts : ChainFacts σ.mem σ.mem L lds bs)
    (hi : i < 2)
    (hwf : ChainOK pc0 (keysG L) bs)
    (hAvoid : WrChainAvoidAbi bs)
    (hKeysOut : KeysOK (keysG (evalBlocks bs (SegEvalState.init L lds)).regs))
    (hRaOut : KeysAvoidRa (evalBlocks bs (SegEvalState.init L lds)).regs)
    (hjal : ∀ (σ' : MState) (i' u' : Nat),
      GoodState σ' → i' < 2 →
      σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) bs) →
      (∃ w, σ'.regs.get? Register.minstret = some w) →
      -- the seg-post memory (so the per-callee jal site lemma can discharge its own
      -- loaded-code precondition off the computed `writeLog`), and the marshalled regs:
      σ'.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log →
      GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      JalStep calleeEntry link σ' i' u') :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel bs + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧
      σ2.regs.get? Register.PC = some calleeEntry ∧
      σ2.regs.get? Register.x1 = some link ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) ∧
      GHolds σ2 (evalBlocks bs (SegEvalState.init L lds)).regs ∧
      σ2.mem = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log ∧
      -- ABI callee-saved frame across the whole bridge (body + jal), FREE:
      (∀ R, AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by
  -- run the seg body (FREE): whole Steps chain, computed end-PC = jalPC, computed
  -- marshalled regs, computed memory, and the raw wrChain frame clause.
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', hmi', hregs, hframe⟩ :=
    segEval_sound bs σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi
  -- the ABI frame of the body, FREE (one `decide` in `hAvoid`).
  have habiBody : ∀ R, AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R :=
    abiFrame_of_wrChain hAvoid hframe
  -- rewrite the seg memory under the pinned entry memory `m0`.
  rw [hmem] at hmem'
  -- take the jal step from the parked config (feeding it the seg-post memory + regs).
  obtain ⟨σ2, i2, hstep2, hi2, hG2, hmem2, hpc2, hra2, hmi2, hnonra2, habiJal⟩ :=
    hjal σ' i' (u + evalBlocksFuel bs) hG' hi' hpc' hmi' hmem' hregs
  refine ⟨σ2, i2, Steps.trans hs (Steps.single hstep2), hi2, hG2, hpc2, hra2, hmi2, ?_, ?_, ?_⟩
  · -- marshalled registers survive the jal (only `x1` written); lift `GHolds` pointwise.
    exact gholds_of_jal hnonra2 _ hKeysOut hRaOut hregs
  · -- memory: the jal changes nothing, so `σ2.mem = σ'.mem = writeLog m0 out.log`.
    rw [hmem2]; exact hmem'
  · -- ABI frame across body ∘ jal (both callee-saved-preserving).
    intro R hR; exact (habiJal R hR).trans (habiBody R hR)

#print axioms bridgeOfSeg

end Vsa.Sim
