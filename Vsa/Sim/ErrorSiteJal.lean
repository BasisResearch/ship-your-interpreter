import Vsa.Sim.ErrorSites
import Vsa.Sim.DivSites2

/-!
# `ErrorSiteJal` — the reusable `jal runtime_error` → `RuntimeErrorAt` marshalling (L6)

The per-error-site recipe (`ErrorSiteRows`/`ErrorSites`) leaves ONE genuinely
per-row but mechanical artefact undischarged: marshalling a `#derive_case`
segment that lands parked at the site's `jal runtime_error` instruction into the
`Triple SitePre (RuntimeErrorAt g inp m0)` that `errHalts_of_site` consumes.  The
plan (`ErrorSites.lean` header) flags this as per-row work "where the site's entry
ghosts meet the computed outcome".

**No site has ever executed that marshalling** — every landed row (`ErrorSiteRows`,
`ErrorSiteRows2`) takes its segment `Triple T` as a HYPOTHESIS.  This file
discharges the *tail half* of that per-site work ONCE, as a reusable combinator:
the single `jal runtime_error` step, marshalled from "parked at the jal PC with
`x10 = inp`, `mem = m0`, and the `g` ghost frame" all the way to `RuntimeErrorAt`.

## What `jalStep_to_runtimeError` collapses

Given the jal instruction's own `(pcJal, word, imm, bytes)` decode data (uniform
shape across all 42 sites; only the concrete PC/offset differ) plus the target
identity `pcJal + sext imm = 0x80002da8` (`runtime_error`'s entry), it produces

```
Triple (JalErrPre …) (fun c' => RuntimeErrorAt g inp m0 c')
```

i.e. from any config parked at the `jal runtime_error` (with the ErrorIn pointer
in `x10`, memory `m0`, callee-saved captured in `g`) one machine step reaches the
`runtime_error` entry with ALL ten `RuntimeErrorAt` conjuncts re-established:

* PC `= 0x80002da8` — `obs_jal_pc` + the target identity;
* `x10 = inp`, `mem = m0`, the loaded images — preserved (jal writes only `x1`/PC);
* the `g` frame — transported across the jal via `post_jal_other` for every
  `NotWrittenJmp` register (which excludes exactly the jal write-set `x1`/PC/…).

So an error-site row now only needs its `#derive_case` *prefix* segment
`Triple SitePre (JalErrPre …)` (byte-pin + decode, the L3 elaborator's job) and
then `Triple.seq prefix jalStep_to_runtimeError` yields the `T` the row assumes —
the per-site marshalling drops from a bespoke ~200-line hand proof to one
`Triple.seq`.  This is the reusable core of the M5 error-site exponentiation
(`experiments/exponentiation-endgame-design.md`, Shape B).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-- **The parked-at-`jal runtime_error` precondition.**  A config sitting at the
site's `jal runtime_error` instruction (PC `pcJal`, bytes `b0..b3`) with the
`RuntimeErrorAt` payload already staged: the ErrorIn pointer `inp` in `x10`,
memory `m0` (carrying the `runtime_error`/`longjmp` images), the callee-saved
ghost frame `g`, and the tick/minstret budget.  This is the post of a site's
`#derive_case` prefix segment; `jalStep_to_runtimeError` runs the one jal step
from here to `RuntimeErrorAt`. -/
def JalErrPre (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ Runtime_errorLoaded m0 ∧ LongjmpLoaded m0 ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some pcJal ∧
  c.σ.regs.get? Register.x10 = some inp ∧
  WinRAM (inp + 16#64) ∧
  (∃ w', c.σ.regs.get? Register.minstret = some w') ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenJmp R → c.σ.regs.get? R = g R) ∧
  c.σ.mem[pcJal.toNat]? = some b0 ∧ c.σ.mem[pcJal.toNat + 1]? = some b1 ∧
  c.σ.mem[pcJal.toNat + 2]? = some b2 ∧ c.σ.mem[pcJal.toNat + 3]? = some b3

/-- **The reusable jal-step marshalling.**  From `JalErrPre` (parked at the site's
`jal runtime_error`) one machine step reaches `RuntimeErrorAt g inp m0` — the
`runtime_error` entry with all ten conjuncts re-established.  The per-site inputs
are exactly the jal instruction's own decode data (`pcJal`, `w`, `imm`, bytes,
`by decide` well-formedness, the `DecodeTable` decode `hdec`, and the target
identity `htgtEq`); the `RuntimeErrorAt` assembly is done here ONCE for all 42
sites. -/
theorem jalStep_to_runtimeError
    (g : (R : Register) → Option (RegisterType R))
    (inp : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (pcJal : BitVec 64) (w : BitVec 32) (imm : BitVec 21)
    (b0 b1 b2 b3 : BitVec 8)
    (hlo : 0x80000000 ≤ pcJal.toNat) (hhi : pcJal.toNat + 4 ≤ tohostAddr)
    (halign : pcJal.toNat % 4 = 0)
    (hnotrvc : Sail.BitVec.extractLsb (((b3.append b2).append b1).append b0) 1 0
      = (0b11#2 : BitVec 2))
    (hword : (((b3.append b2).append b1).append b0) = w)
    (hdec : ∀ σ : MState, GoodState σ →
      (ext_decode w).run (afterPrelude σ)
        = .ok (instruction.JAL (imm, regidx.Regidx 0x01#5)) (afterPrelude σ))
    (htgt : (pcJal + sign_extend (m := 64) imm).toNat % 4 = 0)
    (htgtEq : pcJal + sign_extend (m := 64) imm = (0x80002da8#64 : BitVec 64)) :
    Triple (JalErrPre g inp m0 pcJal b0 b1 b2 b3)
      (fun c' => RuntimeErrorAt g inp m0 c') := by
  intro c hpre
  obtain ⟨hG, hRE, hLJ, hmem, hpc, hx10, hwin, ⟨vm, hminstret⟩, htick, hframe,
    hb0, hb1, hb2, hb3⟩ := hpre
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps pcJal vm w imm (regidx.Regidx 0x01#5) Register.x1
      (BitVec.addInt pcJal 4) b0 b1 b2 b3 hG hpc hminstret hb0 hb1 hb2 hb3
      hlo hhi halign hnotrvc hword (hdec c.σ hG) htgt
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt pcJal 4)) htick
  have hmemσ' : σ'.mem = m0 := hmem'.trans hmem
  refine ⟨⟨σ', i', c.steps + 1⟩, Vsa.Machine.Steps.single hstep, hG', ?_, ?_, hmemσ',
    ?_, ?_, hwin, obs_jal_minstret hobs, hi', ?_⟩
  · -- Runtime_errorLoaded (c'.σ.mem)
    rw [show (⟨σ', i', c.steps + 1⟩ : Config).σ.mem = m0 from hmemσ']; exact hRE
  · -- LongjmpLoaded (c'.σ.mem)
    rw [show (⟨σ', i', c.steps + 1⟩ : Config).σ.mem = m0 from hmemσ']; exact hLJ
  · -- PC = runtime_error entry
    rw [show (⟨σ', i', c.steps + 1⟩ : Config).σ = σ' from rfl, obs_jal_pc hobs, htgtEq]
  · -- x10 = inp (preserved: jal writes only x1/PC)
    exact obs_jal_other hobs Register.x10 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hx10
  · -- the g ghost frame, transported across the jal
    intro R hR
    exact ((hobs.1 R hR.mc hR.mt hR.mip).trans
      (post_jal_other c.σ pcJal vm imm Register.x1 (BitVec.addInt pcJal 4) R
        hR.mi hR.pc hR.1 hR.npc hR.mii)).trans (hframe R hR)

#print axioms jalStep_to_runtimeError

/-! ## The row's `T`, assembled — the per-site marshalling is now one `Triple.seq`

An error-site row's assumed `T : Triple SitePre (RuntimeErrorAt g inp m0)` is now
exactly its `#derive_case` *prefix* (`Triple SitePre (JalErrPre …)` — byte-pin +
decode, emitted by the L3 elaborator) sequenced with `jalStep_to_runtimeError`.
The bespoke ~200-line per-site marshalling collapses to this: -/
example (g : (R : Register) → Option (RegisterType R)) (inp : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {SitePre : Config → Prop}
    (prefix_seg : Triple SitePre (JalErrPre g inp m0 pcJal b0 b1 b2 b3))
    (jal_step : Triple (JalErrPre g inp m0 pcJal b0 b1 b2 b3)
      (fun c' => RuntimeErrorAt g inp m0 c')) :
    Triple SitePre (fun c' => RuntimeErrorAt g inp m0 c') :=
  Triple.seq prefix_seg jal_step

end Vsa.Sim
