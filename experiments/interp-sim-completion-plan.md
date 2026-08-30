# InterpSim completion plan (2026-08-30)

State: `InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam herrFam :
InterpSim L` is a complete theorem. Completion = discharging the four residual
bundles. The v2 metaprogram layer is complete (one combinator per machine-code
shape: `chain_facts`, `#derive_error_site`, `segToTriple`, `loopFromBody`,
`callSeg`), so every remaining leaf is an instance of a shape, not an invention.
Build iteration is ~3x faster post build-speed campaign; decode-table additions
cost ~0.25s/lemma via the generator; `check_all` stage a2 guards elab budgets.

Worktree audit (2026-08-30): the three stale agent worktrees are removed. Two
were byte-identical to work already merged in `35921b2`. The third held a
52-line WIP `eqDispatch_lpins` whose proof was incomplete; its statement is
parked at `experiments/eqne-front-wip-eqDispatch_lpins.lean.txt` for step 1.
`EqNeReprReadback` was orphaned (never imported); now wired into `Vsa.lean`.

Steps, in dependency-and-leverage order. Each lands with `check_all: OK` and
axioms ⊆ {propext, Classical.choice, Quot.sound}; capstones join check_all
THEOREMS as they close.

## 1. eq/ne front wiring (recovers the dead worktree task)

Recipe: `experiments/eqne-front-closure-execution.md` (models named per item).
Build, in order:
1. `eqDispatch_lpins` (statement in the parked WIP file) — bridge
   `evalEqChain_dispatch`'s existential `lds` to the six-elt `[b0..b5]` form
   `EqNeReprReadback`'s repr lemmas expect.
2. `eqnePreBridge` (model: `divPreBridge`, `EvalDivValueTail.lean:47`) — jal →
   `ve_pre g bufa bufb r N φc va vb m0 o c`.
3. `veReturnBridge` (no direct model; spec in the execution doc) —
   `ve_str_post … → VeReturn g (sp-1088) sret vl vr link out0 mEnt`.
4. `EqResid` bundle (model: `DivResid`, `rows/EvalDivRow.lean:662`).
5. `blockC_eqne_front` (model: `blockC_div`, `rows/EvalDivRow.lean:202`) —
   `evalEqChain_dispatch ≫ repr readback ≫ eqnePreBridge ≫
   value_equal_spec_full ≫ veReturnBridge ≫ blockC_eqne`.
6. Reseat `evalEqNeSim` to div-parity (model: `evalDivSim`,
   `rows/EvalDivRow.lean:751`); keep `evalEqSim`/`evalNeSim` thin.
Gate: `#print axioms evalEqSim evalNeSim` clean; add to check_all.

## 2. Last binary ops: ge, mul

- `ge`: lt/le/gt clone; xori decode landed (`d7d6ec5`) unblocked it. Note the
  flagged `.ge` spec/machine divergence in PLAN-InterpSim (token 23 arm):
  resolve the semantics decision BEFORE proving (desugar `>=` vs error-arm).
- `mul`: resume `experiments/mul-wip/` (captured at `55f90ed`). The two missing
  decode lemmas (`decode_42d81c63`, `decode_3d051a63`) are now generator
  entries (fast template). Remaining: bind `hmi2`, thread the sailOutput `o`
  field per the A-blocker pattern (already done for div/mod — clone).
After this every `EvalE` constructor has a landed Triple: `htri` leaf
inventory complete.

## 3. M5 error family routing (cheapest bundle, closes `herrFam`)

All 19 distinct error-site Triples are proved (`rows/ErrSitesBatch{0..3}`,
`errSite_<pc>`). Remaining is routing, no new machine proofs:
- map each `errorSimFull` minor premise → its `errSite_<pc>` (SitePre/hsite);
- supply the shared `SC`/`HT` facts ONCE at L7/L8 (same for all 42 premises).
Also in this area: fix and land `Vsa/Sim/ExitPathSpans.lean` (untracked,
broken at `c.σ` field resolution ~line 156) — it discharges `InterpContSeg`
of the exit-70 tail; `ExitPathSeg` shows the working idiom.

## 4. Shape-C loop fan-out (`loopFromBody`)

The per-iteration step contracts listed as residuals — `ExecWhileStep`,
`ExecForStep`, `EvalArgsStep`, block-`hstep` — are each `Triple.loop` over one
back-edge block. One invariant+measure per loop SHAPE (not per site), bodies
emitted by `loopFromBody` (`DeriveLoop.lean`). Env-scan loops (env_get/
env_define) share the scan shape; `env_get_found`'s `hreach` residual closes
here too (unblocks unconditional `evalVarSim`).

## 5. Shape-D: composed `env_define`/`realloc` contract (biggest semantic gap)

Gates `Call.closure`, `varDecl`, `assign`. Compose via `callSeg`/`callSegConseq`
(`DeriveCallSeg.lean`): M3's env_define prologue ≫ strlen_spec ≫ MallocSpec
(named hypothesis per the Layer-2 decision — NOT an axiom) ≫ memcpy ≫ realloc
(`ReallocSpec.lean`: `ReallocOps`/`ReallocPre`/`ReallocPost`/grow2 arena lemmas
exist; the machine-level realloc row is the main new proof). Then `Call.closure`
= arity+depth-guard+env_new+env_define-fold+body-ExecSeq at d+1, all seams
`Triple.seq`.

## 6. Residual unification → mutual-recursor assembly (`hterm`, `htri`)

Normalize every case's heterogeneous named residuals into the four-bundle
interface — the `DivResid`→`EqResid` pattern is the template: each case's
residual becomes one named `<Op>Resid` Prop threaded through its row. Then the
`@EvalE.rec`/`InductionScaffold` assembly is a table: motive = the `EvalIH`
shape, each arm supplied by its row. This is the step PLAN-InterpSim flags as
"blocked on residual unification"; the unblocntion is naming discipline, not
new machine proofs.

## 7. M5 second half + M6 close

- `Approx` trichotomy + divergence simulation (per-piece plan in
  `memory/m5-stuck-sim.md`): every spec rule costs ≥1 instruction; resource
  exhaustion (depth cap 1000, arena) lands in the `Halts e ≠ 0` disjunct.
- M6: bundle `ImageStaticsLoaded` (statics) + capstone geometry into the
  concrete `Layout L` record (`LayoutInstance.lean` already pins
  Layout+GeomFacts), plug into `Vsa.Refine.refinement`, final
  `#print axioms` audit, add the end-to-end theorem to check_all.

## Execution notes

- Fan-out mechanics: COW-clone worktree workflow (proven on the error-site
  fan-out) for independent rows; ≤3 concurrent lean; agents use
  `lake env lean` only, never `lake build`, never LSP (spawns a racing build).
- Steps 1-2 are independent of 3; 4 and 5 are independent of each other;
  6 needs 1-5; 7 needs 6 (term_sim side) but 3 (error family) can start now.
- Standing rule: run `scripts/abs_inventory.sh` before every dispatch; reuse
  by name, never reinvent.
