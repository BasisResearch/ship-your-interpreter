import Vsa.Sim.Muldi3Spec
import Vsa.Sim.StepJump
import Vsa.Sim.MemcpySpec
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec

/-!
# `ObsAvoid` — bundled `obs_*_other` register-frame consumers (one `decide` per site)

## The wall this pays off

The tree-wide elaboration wall (`experiments/decision-census-patterns.md`) is the
hand-threaded StepObs `obs_*_other` consumer family. Every such call reads one GPR
`R` off the next machine state through an observation and pays a **register-frame
disequality ladder** — 7 or 8 separate `(by decide)` arguments, each proving one
ground `(Register.K == R) = false`:

    obs_alu_other hobs1 Register.x2
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) hx2         -- 8 decides!

`obs_alu_other` alone consumes **~17.5k** such `(by decide)` blocks across 24 hot
files (`Muldi3Spec.lean:330`); the whole `obs_*_other` family is ~30k. Each
`(by decide)` pays the elaborator's per-call `Decidable`-instance / `whnf` setup
cost, so 8 of them per site is 8× that fixed overhead for what is morally ONE
ground fact.

## What this file provides

For each base `obs_*_other` lemma, a bundled variant `<base>'` whose conclusion,
implicit arguments, and explicit argument ORDER match the base VERBATIM — except the
7-8 disequality hypotheses are replaced by a single `(hdis : … ∧ … ∧ …)` conjunction
closed at the callsite by ONE `(by decide)`. The variant destructures `hdis` with
`.1`/`.2.1`/… projections and forwards to the base. Callsites become:

    obs_alu_other' hobs1 Register.x2 (by decide) hx2                -- 1 decide

so a plain drop-in that cuts 8→1 (alu/jal) or 7→1 (store/branch/jr) decides per site.

## Form choice — why an `∧`-conjunction discharged by one `decide` (not a `Bool` fold)

Two candidate bundle forms were considered (see `fast-reflection-rules` and the
design in `experiments/snprintf17-rewrite-design.md` §H1):

1. **`Bool`-fold**: `(hdis : (R != mcycle && R != mtime && …) = true)` + a custom
   `avoids`/`ne_of_avoids` extraction layer.
2. **`∧`-conjunction of the base's OWN conjuncts** (chosen):
   `(hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧ …)`.

Form 2 is chosen because the conjuncts are the base lemma's arguments spelled
**identically** — extraction is pure `And` projection (`.1`, `.2.1`, …), a
zero-cost term-level operation with NO symmetry lemma (`!=` vs `==`), NO membership
lemma, and NO `whnf`. The bundle is discharged by a single ground `decide` reducing a
short `Bool`-`and` of `Register.decEq` on two concrete register literals — a bounded
kernel reduction, strictly cheaper than the 7-8 separate `decide` elaborations it
replaces (`fast-reflection-rules` rules 1/6/7: reflect on a small first-order term, no
typeclass search, no big `whnf`). Form 1's `Bool` fold would force a `(X == R) = false
↔ (R != X) = true` bridge at every projection — more work, not less.

## Placement in the import DAG (no cycles)

`readback` and the `post_*_other` frame lemmas all live in `Muldi3Spec`; the
`get?_sigmaPost_*` frame lemmas live even lower (`StepStore`/`StepBranch`). The base
`obs_*_other` lemmas are scattered across `Muldi3Spec` (alu/branch/jr),
`DivSites2` (jal), `MemcpySpec` (store), `ValueSpec` (store_val),
`ValueTruthySpec` (branch_taken/nottaken). This file imports exactly those five base
files — verified (`experiments/obs-bundle-notes.md`) that NONE of them reaches any of
the 24 consumer files, so every consumer can `import Vsa.Sim.ObsAvoid` with no cycle.

`SnprintfSpec4` is deliberately NOT imported (it reaches consumer `DivSpec3` → would
cycle). Its `obs_store_other_sn4` / `obs_store_other_sn3` (SnprintfSpec3) variants are
therefore **restated standalone** here (`obs_store_other_sn4'` / `_sn3'`) directly from
`readback`-level primitives (`hobs.1` + `get?_sigmaPost_store`), giving a drop-in that
needs no SnprintfSpec3/4 import. Their bodies are byte-for-byte the bases' bodies.

## Callsite recipe

    -- 8-diseq family (alu, jal): 8 `(by decide)` → 1
    obs_alu_other'  hobs R (by decide) hσ
    obs_jal_other'  hobs R (by decide) hσ
    -- 7-diseq family (store/branch/jr), `hobs R` order: 7 `(by decide)` → 1
    obs_store_other'            hobs R (by decide) hσ
    obs_store_other_val'        hobs R (by decide) hσ
    obs_btaken_other'           hobs R (by decide) hσ
    obs_bnottaken_other'        hobs R (by decide) hσ
    obs_jr_other'               hobs R (by decide) hσ
    obs_branch_taken_other'     hobs R (by decide) hσ
    obs_branch_nottaken_other'  hobs R (by decide) hσ
    -- 7-diseq store copies, `R hobs` order (Snprintf): 7 `(by decide)` → 1
    obs_store_other_sn4' R hobs (by decide) hσ
    obs_store_other_sn3' R hobs (by decide) hσ

The mechanical rewriter `scripts/apply_obs_bundle.py` performs these substitutions.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 4000000

namespace Vsa.Sim

/-! ## 8-disequality family (`rd`/`rd_reg == R` present) — 8 `(by decide)` → 1 -/

/-- Bundled `obs_alu_other`: the 8-way register-disequality ladder folded into one
`∧`-hypothesis, closed at the callsite by a single ground `decide` (both `rd` and `R`
are concrete literals). Conclusion + argument order match `obs_alu_other` verbatim. -/
theorem obs_alu_other' {σ' σ : MState} {pc vm : BitVec 64} {rd : Register}
    {v : RegisterType rd} (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v))
    (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (rd == R) = false ∧
            (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_alu_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2.1 hdis.2.2.2.2.2.2.2 hσ

/-- Bundled `obs_jal_other` (`DivSites2`): 8-way ladder → one `∧`-`decide`.
Restated STANDALONE from `readback` (`Muldi3Spec`) + `get?_sigmaPost_jal`
(`StepJump`) rather than forwarding to `DivSites2.obs_jal_other` — importing
`DivSites2` would drag `DivSpec` (via `DivLoops`) into every consumer's scope,
and `DivSpec`'s namespace-generic `abbrev Frame` shadows `While.Frame` in
`Vsa.Sim`-namespace consumers (broke `EnvNewSpec`). Body is the base's body. -/
theorem obs_jal_other' {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (rd_reg == R) = false ∧
            (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hdis.1 hdis.2.1 hdis.2.2.1
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R hdis.2.2.2.1 hdis.2.2.2.2.1
      hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2.1 hdis.2.2.2.2.2.2.2).trans hσ)

/-! ## 7-disequality family, `hobs R` argument order — 7 `(by decide)` → 1 -/

/-- Bundled `obs_store_other` (`MemcpySpec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_store_other' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_store_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_store_other_val` (`ValueSpec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_store_other_val' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_store_other_val hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_btaken_other` (`Muldi3Spec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_btaken_other' {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_btaken_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_bnottaken_other` (`Muldi3Spec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_bnottaken_other' {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_bnottaken_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_jr_other` (`Muldi3Spec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_jr_other' {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_jr_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_branch_taken_other` (`ValueTruthySpec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_branch_taken_other' {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_branch_taken_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-- Bundled `obs_branch_nottaken_other` (`ValueTruthySpec`): 7-way ladder → one `∧`-`decide`. -/
theorem obs_branch_nottaken_other' {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    {w : RegisterType R}
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  obs_branch_nottaken_other hobs R hdis.1 hdis.2.1 hdis.2.2.1 hdis.2.2.2.1 hdis.2.2.2.2.1
    hdis.2.2.2.2.2.1 hdis.2.2.2.2.2.2 hσ

/-! ## 7-disequality store copies, `R hobs` argument order (Snprintf)

`obs_store_other_sn4` (SnprintfSpec4) and `obs_store_other_sn3` (SnprintfSpec3) take
`R` BEFORE `hobs`. Those defining files are NOT imported (SnprintfSpec4 reaches
consumer `DivSpec3` → would cycle), so these two are **restated standalone** — their
bodies are the bases' bodies verbatim (`hobs.1` read-back + `get?_sigmaPost_store`
frame), reachable here via `Muldi3Spec → StepObs → StepStore`. -/

/-- Bundled standalone copy of `obs_store_other_sn4`: `R hobs` order, 7-way ladder →
one `∧`-`decide`. -/
theorem obs_store_other_sn4' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w := by
  obtain ⟨hmc, hmt, hmi, h1, h2, h4, h5⟩ := hdis
  rw [hobs.1 R hmc hmt hmi]
  rw [get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5]; exact hσ

/-- Bundled standalone copy of `obs_store_other_sn3`: `R hobs` order, 7-way ladder →
one `∧`-`decide`. Identical to `obs_store_other_sn4'`; a separate name so the rewriter
maps each base head to its own primed head. -/
theorem obs_store_other_sn3' {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)} (R : Register) {w : RegisterType R}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m'))
    (hdis : (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
            (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
            (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
            (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w := by
  obtain ⟨hmc, hmt, hmi, h1, h2, h4, h5⟩ := hdis
  rw [hobs.1 R hmc hmt hmi]
  rw [get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5]; exact hσ

end Vsa.Sim
